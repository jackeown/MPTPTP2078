%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:04 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 148 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  107 ( 449 expanded)
%              Number of equality atoms :    3 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v1_tops_2(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                     => ( D = B
                       => v1_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_18,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_16,plain,(
    ~ v1_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ~ v1_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_35,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_41,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_59,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_55)
      | v1_tops_2(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54))))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_29,c_59])).

tff(c_66,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v1_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_61])).

tff(c_67,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_66])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    v1_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    ! [A_45,C_46,B_47] :
      ( m1_subset_1(A_45,C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_112,plain,(
    ! [C_68,A_69,B_70] :
      ( v3_pre_topc(C_68,A_69)
      | ~ r2_hidden(C_68,B_70)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ v1_tops_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_134,plain,(
    ! [A_74] :
      ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),A_74)
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ v1_tops_2('#skF_3',A_74)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_74))))
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_67,c_112])).

tff(c_142,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_153,plain,(
    v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_28,c_26,c_22,c_142])).

tff(c_47,plain,(
    ! [A_45] :
      ( m1_subset_1(A_45,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_29,c_42])).

tff(c_84,plain,(
    ! [D_63,C_64,A_65] :
      ( v3_pre_topc(D_63,C_64)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0(C_64)))
      | ~ v3_pre_topc(D_63,A_65)
      | ~ m1_pre_topc(C_64,A_65)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_116,plain,(
    ! [A_71,A_72] :
      ( v3_pre_topc(A_71,'#skF_4')
      | ~ v3_pre_topc(A_71,A_72)
      | ~ m1_pre_topc('#skF_4',A_72)
      | ~ m1_subset_1(A_71,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ r2_hidden(A_71,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_47,c_84])).

tff(c_122,plain,(
    ! [A_45] :
      ( v3_pre_topc(A_45,'#skF_4')
      | ~ v3_pre_topc(A_45,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_48,c_116])).

tff(c_129,plain,(
    ! [A_45] :
      ( v3_pre_topc(A_45,'#skF_4')
      | ~ v3_pre_topc(A_45,'#skF_2')
      | ~ r2_hidden(A_45,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_122])).

tff(c_159,plain,
    ( v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_153,c_129])).

tff(c_162,plain,(
    v3_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_159])).

tff(c_8,plain,(
    ! [A_7,B_13] :
      ( ~ v3_pre_topc('#skF_1'(A_7,B_13),A_7)
      | v1_tops_2(B_13,A_7)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_164,plain,
    ( v1_tops_2('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_162,c_8])).

tff(c_167,plain,(
    v1_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.22  %$ v3_pre_topc > v1_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.04/1.22  
% 2.04/1.22  %Foreground sorts:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Background operators:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Foreground operators:
% 2.04/1.22  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.22  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.04/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.04/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.04/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.04/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.04/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.22  
% 2.04/1.23  tff(f_87, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v1_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v1_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_2)).
% 2.04/1.23  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.04/1.23  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 2.04/1.23  tff(f_31, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.04/1.23  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 2.04/1.23  tff(c_18, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.23  tff(c_16, plain, (~v1_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.23  tff(c_30, plain, (~v1_tops_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 2.04/1.23  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.23  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.23  tff(c_35, plain, (![B_43, A_44]: (l1_pre_topc(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.04/1.23  tff(c_38, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.04/1.23  tff(c_41, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.04/1.23  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.23  tff(c_29, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.04/1.23  tff(c_59, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), B_55) | v1_tops_2(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54)))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.23  tff(c_61, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3') | v1_tops_2('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_29, c_59])).
% 2.04/1.23  tff(c_66, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3') | v1_tops_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_61])).
% 2.04/1.23  tff(c_67, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_66])).
% 2.04/1.23  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.23  tff(c_22, plain, (v1_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.04/1.23  tff(c_42, plain, (![A_45, C_46, B_47]: (m1_subset_1(A_45, C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.23  tff(c_48, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_45, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_42])).
% 2.04/1.23  tff(c_112, plain, (![C_68, A_69, B_70]: (v3_pre_topc(C_68, A_69) | ~r2_hidden(C_68, B_70) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~v1_tops_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69)))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.23  tff(c_134, plain, (![A_74]: (v3_pre_topc('#skF_1'('#skF_4', '#skF_3'), A_74) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_74))) | ~v1_tops_2('#skF_3', A_74) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_74)))) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_67, c_112])).
% 2.04/1.23  tff(c_142, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_2') | ~v1_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_48, c_134])).
% 2.04/1.23  tff(c_153, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_28, c_26, c_22, c_142])).
% 2.04/1.23  tff(c_47, plain, (![A_45]: (m1_subset_1(A_45, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden(A_45, '#skF_3'))), inference(resolution, [status(thm)], [c_29, c_42])).
% 2.04/1.23  tff(c_84, plain, (![D_63, C_64, A_65]: (v3_pre_topc(D_63, C_64) | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0(C_64))) | ~v3_pre_topc(D_63, A_65) | ~m1_pre_topc(C_64, A_65) | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0(A_65))) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.04/1.23  tff(c_116, plain, (![A_71, A_72]: (v3_pre_topc(A_71, '#skF_4') | ~v3_pre_topc(A_71, A_72) | ~m1_pre_topc('#skF_4', A_72) | ~m1_subset_1(A_71, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~r2_hidden(A_71, '#skF_3'))), inference(resolution, [status(thm)], [c_47, c_84])).
% 2.04/1.23  tff(c_122, plain, (![A_45]: (v3_pre_topc(A_45, '#skF_4') | ~v3_pre_topc(A_45, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r2_hidden(A_45, '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_116])).
% 2.04/1.23  tff(c_129, plain, (![A_45]: (v3_pre_topc(A_45, '#skF_4') | ~v3_pre_topc(A_45, '#skF_2') | ~r2_hidden(A_45, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_122])).
% 2.04/1.23  tff(c_159, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_153, c_129])).
% 2.04/1.23  tff(c_162, plain, (v3_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_159])).
% 2.04/1.23  tff(c_8, plain, (![A_7, B_13]: (~v3_pre_topc('#skF_1'(A_7, B_13), A_7) | v1_tops_2(B_13, A_7) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7)))) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.04/1.23  tff(c_164, plain, (v1_tops_2('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_162, c_8])).
% 2.04/1.23  tff(c_167, plain, (v1_tops_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_29, c_164])).
% 2.04/1.23  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_167])).
% 2.04/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  Inference rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Ref     : 0
% 2.04/1.23  #Sup     : 27
% 2.04/1.23  #Fact    : 0
% 2.04/1.23  #Define  : 0
% 2.04/1.23  #Split   : 2
% 2.04/1.23  #Chain   : 0
% 2.04/1.23  #Close   : 0
% 2.04/1.23  
% 2.04/1.23  Ordering : KBO
% 2.04/1.23  
% 2.04/1.23  Simplification rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Subsume      : 5
% 2.04/1.23  #Demod        : 23
% 2.04/1.23  #Tautology    : 5
% 2.04/1.23  #SimpNegUnit  : 3
% 2.04/1.23  #BackRed      : 0
% 2.04/1.23  
% 2.04/1.23  #Partial instantiations: 0
% 2.04/1.23  #Strategies tried      : 1
% 2.04/1.23  
% 2.04/1.23  Timing (in seconds)
% 2.04/1.23  ----------------------
% 2.04/1.23  Preprocessing        : 0.30
% 2.04/1.23  Parsing              : 0.16
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.18
% 2.04/1.23  Inferencing          : 0.07
% 2.04/1.23  Reduction            : 0.05
% 2.04/1.23  Demodulation         : 0.04
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.04
% 2.04/1.24  Abstraction          : 0.01
% 2.04/1.24  MUC search           : 0.00
% 2.04/1.24  Cooper               : 0.00
% 2.04/1.24  Total                : 0.51
% 2.04/1.24  Index Insertion      : 0.00
% 2.04/1.24  Index Deletion       : 0.00
% 2.04/1.24  Index Matching       : 0.00
% 2.04/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
