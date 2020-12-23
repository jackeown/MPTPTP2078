%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:04 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 137 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 451 expanded)
%              Number of equality atoms :    3 (  39 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v2_tops_2(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C))))
                     => ( D = B
                       => v2_tops_2(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_18,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ~ v2_tops_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    ~ v2_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_35,plain,(
    ! [B_47,A_48] :
      ( l1_pre_topc(B_47)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_41,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_29,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_22,plain,(
    v2_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1('#skF_1'(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | v2_tops_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [C_10,A_4,B_8] :
      ( m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(u1_struct_0(B_8)))
      | ~ m1_pre_topc(B_8,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_59,plain,(
    ! [A_56,B_57,A_4] :
      ( m1_subset_1('#skF_1'(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_pre_topc(A_56,A_4)
      | ~ l1_pre_topc(A_4)
      | v2_tops_2(B_57,A_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_56,c_4])).

tff(c_44,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_55)
      | v2_tops_2(B_55,A_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54))))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_29,c_44])).

tff(c_51,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_46])).

tff(c_52,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_51])).

tff(c_64,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_pre_topc(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ v2_tops_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,(
    ! [A_67] :
      ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),A_67)
      | ~ m1_subset_1('#skF_1'('#skF_4','#skF_3'),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ v2_tops_2('#skF_3',A_67)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67))))
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_52,c_64])).

tff(c_79,plain,(
    ! [A_4] :
      ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),A_4)
      | ~ v2_tops_2('#skF_3',A_4)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ m1_pre_topc('#skF_4',A_4)
      | ~ l1_pre_topc(A_4)
      | v2_tops_2('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_59,c_75])).

tff(c_86,plain,(
    ! [A_4] :
      ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),A_4)
      | ~ v2_tops_2('#skF_3',A_4)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4))))
      | ~ m1_pre_topc('#skF_4',A_4)
      | ~ l1_pre_topc(A_4)
      | v2_tops_2('#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_79])).

tff(c_92,plain,(
    ! [A_68] :
      ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),A_68)
      | ~ v2_tops_2('#skF_3',A_68)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68))))
      | ~ m1_pre_topc('#skF_4',A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_86])).

tff(c_98,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2')
    | ~ v2_tops_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_104,plain,(
    v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_98])).

tff(c_12,plain,(
    ! [A_11,B_17] :
      ( m1_subset_1('#skF_1'(A_11,B_17),k1_zfmisc_1(u1_struct_0(A_11)))
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_60,plain,(
    ! [D_58,C_59,A_60] :
      ( v4_pre_topc(D_58,C_59)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(C_59)))
      | ~ v4_pre_topc(D_58,A_60)
      | ~ m1_pre_topc(C_59,A_60)
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_142,plain,(
    ! [A_78,B_79,A_80] :
      ( v4_pre_topc('#skF_1'(A_78,B_79),A_78)
      | ~ v4_pre_topc('#skF_1'(A_78,B_79),A_80)
      | ~ m1_pre_topc(A_78,A_80)
      | ~ m1_subset_1('#skF_1'(A_78,B_79),k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | v2_tops_2(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_12,c_60])).

tff(c_157,plain,(
    ! [A_81,B_82,A_83] :
      ( v4_pre_topc('#skF_1'(A_81,B_82),A_81)
      | ~ v4_pre_topc('#skF_1'(A_81,B_82),A_83)
      | ~ m1_pre_topc(A_81,A_83)
      | ~ l1_pre_topc(A_83)
      | v2_tops_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81))))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_59,c_142])).

tff(c_159,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_tops_2('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_157])).

tff(c_162,plain,
    ( v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4')
    | v2_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_28,c_24,c_159])).

tff(c_163,plain,(
    v4_pre_topc('#skF_1'('#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_162])).

tff(c_8,plain,(
    ! [A_11,B_17] :
      ( ~ v4_pre_topc('#skF_1'(A_11,B_17),A_11)
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_167,plain,
    ( v2_tops_2('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_163,c_8])).

tff(c_174,plain,(
    v2_tops_2('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_29,c_167])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:54:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.24  
% 2.23/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.24  %$ v4_pre_topc > v2_tops_2 > r2_hidden > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.23/1.24  
% 2.23/1.24  %Foreground sorts:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Background operators:
% 2.23/1.24  
% 2.23/1.24  
% 2.23/1.24  %Foreground operators:
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.24  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.23/1.24  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.23/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.24  
% 2.23/1.26  tff(f_91, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_pre_topc(C, A) => (v2_tops_2(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(C)))) => ((D = B) => v2_tops_2(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tops_2)).
% 2.23/1.26  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.23/1.26  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_2)).
% 2.23/1.26  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.23/1.26  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 2.23/1.26  tff(c_18, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.26  tff(c_16, plain, (~v2_tops_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.26  tff(c_30, plain, (~v2_tops_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16])).
% 2.23/1.26  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.26  tff(c_24, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.26  tff(c_35, plain, (![B_47, A_48]: (l1_pre_topc(B_47) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.26  tff(c_38, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.23/1.26  tff(c_41, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.23/1.26  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.26  tff(c_29, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.23/1.26  tff(c_22, plain, (v2_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.26  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.23/1.26  tff(c_56, plain, (![A_56, B_57]: (m1_subset_1('#skF_1'(A_56, B_57), k1_zfmisc_1(u1_struct_0(A_56))) | v2_tops_2(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.26  tff(c_4, plain, (![C_10, A_4, B_8]: (m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_subset_1(C_10, k1_zfmisc_1(u1_struct_0(B_8))) | ~m1_pre_topc(B_8, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.26  tff(c_59, plain, (![A_56, B_57, A_4]: (m1_subset_1('#skF_1'(A_56, B_57), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_pre_topc(A_56, A_4) | ~l1_pre_topc(A_4) | v2_tops_2(B_57, A_56) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~l1_pre_topc(A_56))), inference(resolution, [status(thm)], [c_56, c_4])).
% 2.23/1.26  tff(c_44, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), B_55) | v2_tops_2(B_55, A_54) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_54)))) | ~l1_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.26  tff(c_46, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_29, c_44])).
% 2.23/1.26  tff(c_51, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_46])).
% 2.23/1.26  tff(c_52, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_51])).
% 2.23/1.26  tff(c_64, plain, (![C_61, A_62, B_63]: (v4_pre_topc(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(C_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~v2_tops_2(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.26  tff(c_75, plain, (![A_67]: (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), A_67) | ~m1_subset_1('#skF_1'('#skF_4', '#skF_3'), k1_zfmisc_1(u1_struct_0(A_67))) | ~v2_tops_2('#skF_3', A_67) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67)))) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_52, c_64])).
% 2.23/1.26  tff(c_79, plain, (![A_4]: (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), A_4) | ~v2_tops_2('#skF_3', A_4) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~m1_pre_topc('#skF_4', A_4) | ~l1_pre_topc(A_4) | v2_tops_2('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_59, c_75])).
% 2.23/1.26  tff(c_86, plain, (![A_4]: (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), A_4) | ~v2_tops_2('#skF_3', A_4) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_4)))) | ~m1_pre_topc('#skF_4', A_4) | ~l1_pre_topc(A_4) | v2_tops_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_29, c_79])).
% 2.23/1.26  tff(c_92, plain, (![A_68]: (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), A_68) | ~v2_tops_2('#skF_3', A_68) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_68)))) | ~m1_pre_topc('#skF_4', A_68) | ~l1_pre_topc(A_68))), inference(negUnitSimplification, [status(thm)], [c_30, c_86])).
% 2.23/1.26  tff(c_98, plain, (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_2') | ~v2_tops_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_92])).
% 2.23/1.26  tff(c_104, plain, (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_22, c_98])).
% 2.23/1.26  tff(c_12, plain, (![A_11, B_17]: (m1_subset_1('#skF_1'(A_11, B_17), k1_zfmisc_1(u1_struct_0(A_11))) | v2_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.26  tff(c_60, plain, (![D_58, C_59, A_60]: (v4_pre_topc(D_58, C_59) | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0(C_59))) | ~v4_pre_topc(D_58, A_60) | ~m1_pre_topc(C_59, A_60) | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.26  tff(c_142, plain, (![A_78, B_79, A_80]: (v4_pre_topc('#skF_1'(A_78, B_79), A_78) | ~v4_pre_topc('#skF_1'(A_78, B_79), A_80) | ~m1_pre_topc(A_78, A_80) | ~m1_subset_1('#skF_1'(A_78, B_79), k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | v2_tops_2(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78)))) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_12, c_60])).
% 2.23/1.26  tff(c_157, plain, (![A_81, B_82, A_83]: (v4_pre_topc('#skF_1'(A_81, B_82), A_81) | ~v4_pre_topc('#skF_1'(A_81, B_82), A_83) | ~m1_pre_topc(A_81, A_83) | ~l1_pre_topc(A_83) | v2_tops_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81)))) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_59, c_142])).
% 2.23/1.26  tff(c_159, plain, (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_tops_2('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_104, c_157])).
% 2.23/1.26  tff(c_162, plain, (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_4') | v2_tops_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_29, c_28, c_24, c_159])).
% 2.23/1.26  tff(c_163, plain, (v4_pre_topc('#skF_1'('#skF_4', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_30, c_162])).
% 2.23/1.26  tff(c_8, plain, (![A_11, B_17]: (~v4_pre_topc('#skF_1'(A_11, B_17), A_11) | v2_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.26  tff(c_167, plain, (v2_tops_2('#skF_3', '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_163, c_8])).
% 2.23/1.26  tff(c_174, plain, (v2_tops_2('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_29, c_167])).
% 2.23/1.26  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_174])).
% 2.23/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  Inference rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Ref     : 0
% 2.23/1.26  #Sup     : 28
% 2.23/1.26  #Fact    : 0
% 2.23/1.26  #Define  : 0
% 2.23/1.26  #Split   : 1
% 2.23/1.26  #Chain   : 0
% 2.23/1.26  #Close   : 0
% 2.23/1.26  
% 2.23/1.26  Ordering : KBO
% 2.23/1.26  
% 2.23/1.26  Simplification rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Subsume      : 5
% 2.23/1.26  #Demod        : 34
% 2.23/1.26  #Tautology    : 4
% 2.23/1.26  #SimpNegUnit  : 8
% 2.23/1.26  #BackRed      : 0
% 2.23/1.26  
% 2.23/1.26  #Partial instantiations: 0
% 2.23/1.26  #Strategies tried      : 1
% 2.23/1.26  
% 2.23/1.26  Timing (in seconds)
% 2.23/1.26  ----------------------
% 2.23/1.26  Preprocessing        : 0.30
% 2.23/1.26  Parsing              : 0.16
% 2.23/1.26  CNF conversion       : 0.02
% 2.23/1.26  Main loop            : 0.20
% 2.23/1.26  Inferencing          : 0.07
% 2.23/1.26  Reduction            : 0.05
% 2.23/1.26  Demodulation         : 0.04
% 2.23/1.26  BG Simplification    : 0.01
% 2.23/1.26  Subsumption          : 0.05
% 2.23/1.26  Abstraction          : 0.01
% 2.23/1.26  MUC search           : 0.00
% 2.23/1.26  Cooper               : 0.00
% 2.23/1.26  Total                : 0.53
% 2.23/1.26  Index Insertion      : 0.00
% 2.23/1.26  Index Deletion       : 0.00
% 2.23/1.26  Index Matching       : 0.00
% 2.23/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
