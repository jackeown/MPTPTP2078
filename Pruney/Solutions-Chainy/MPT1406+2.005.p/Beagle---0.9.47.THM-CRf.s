%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:35 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   59 (  92 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 227 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_connsp_2(C,A,B)
               => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_122,plain,(
    ! [C_60,A_61,B_62] :
      ( m1_subset_1(C_60,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m2_connsp_2(C_60,A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_124,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_127,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_124])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_127,c_8])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_307,plain,(
    ! [B_75,A_76,C_77] :
      ( r1_tarski(B_75,k1_tops_1(A_76,C_77))
      | ~ m2_connsp_2(C_77,A_76,B_75)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76)
      | ~ v2_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_376,plain,(
    ! [B_85,A_86,A_87] :
      ( r1_tarski(B_85,k1_tops_1(A_86,A_87))
      | ~ m2_connsp_2(A_87,A_86,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | ~ r1_tarski(A_87,u1_struct_0(A_86)) ) ),
    inference(resolution,[status(thm)],[c_10,c_307])).

tff(c_387,plain,(
    ! [A_87] :
      ( r1_tarski('#skF_2',k1_tops_1('#skF_1',A_87))
      | ~ m2_connsp_2(A_87,'#skF_1','#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(A_87,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_376])).

tff(c_458,plain,(
    ! [A_94] :
      ( r1_tarski('#skF_2',k1_tops_1('#skF_1',A_94))
      | ~ m2_connsp_2(A_94,'#skF_1','#skF_2')
      | ~ r1_tarski(A_94,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_387])).

tff(c_470,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_142,c_458])).

tff(c_482,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_470])).

tff(c_14,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_tops_1(A_11,B_13),B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_131,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_14])).

tff(c_140,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_131])).

tff(c_4,plain,(
    ! [A_3] : ~ v1_xboole_0(k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(k1_zfmisc_1(A_1),k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_46,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_42,B_43,A_44] :
      ( m1_subset_1(A_42,B_43)
      | ~ r2_hidden(A_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_10,c_46])).

tff(c_69,plain,(
    ! [A_49,B_50,B_51] :
      ( m1_subset_1(A_49,B_50)
      | ~ r1_tarski(B_51,B_50)
      | v1_xboole_0(B_51)
      | ~ m1_subset_1(A_49,B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_75,plain,(
    ! [A_49,B_2,A_1] :
      ( m1_subset_1(A_49,k1_zfmisc_1(B_2))
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_49,k1_zfmisc_1(A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_85,plain,(
    ! [A_52,B_53,A_54] :
      ( m1_subset_1(A_52,k1_zfmisc_1(B_53))
      | ~ m1_subset_1(A_52,k1_zfmisc_1(A_54))
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4,c_75])).

tff(c_90,plain,(
    ! [A_6,B_53,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_53))
      | ~ r1_tarski(B_7,B_53)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_153,plain,(
    ! [A_6] :
      ( m1_subset_1(A_6,k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(A_6,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_140,c_90])).

tff(c_498,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_482,c_153])).

tff(c_511,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_498,c_8])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.40  
% 2.91/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.40  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.91/1.40  
% 2.91/1.40  %Foreground sorts:
% 2.91/1.40  
% 2.91/1.40  
% 2.91/1.40  %Background operators:
% 2.91/1.40  
% 2.91/1.40  
% 2.91/1.40  %Foreground operators:
% 2.91/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.91/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.91/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.91/1.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.91/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.91/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.91/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.91/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.91/1.40  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 2.91/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.91/1.40  
% 2.91/1.41  tff(f_96, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_connsp_2)).
% 2.91/1.41  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 2.91/1.41  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.91/1.41  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 2.91/1.41  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 2.91/1.41  tff(f_32, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.91/1.41  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.91/1.41  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.91/1.41  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.91/1.41  tff(c_22, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.41  tff(c_24, plain, (m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.41  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.41  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.41  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.91/1.41  tff(c_122, plain, (![C_60, A_61, B_62]: (m1_subset_1(C_60, k1_zfmisc_1(u1_struct_0(A_61))) | ~m2_connsp_2(C_60, A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.91/1.41  tff(c_124, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_122])).
% 2.91/1.41  tff(c_127, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_124])).
% 2.91/1.41  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.91/1.41  tff(c_142, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_127, c_8])).
% 2.91/1.41  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.91/1.41  tff(c_307, plain, (![B_75, A_76, C_77]: (r1_tarski(B_75, k1_tops_1(A_76, C_77)) | ~m2_connsp_2(C_77, A_76, B_75) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76) | ~v2_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.91/1.41  tff(c_376, plain, (![B_85, A_86, A_87]: (r1_tarski(B_85, k1_tops_1(A_86, A_87)) | ~m2_connsp_2(A_87, A_86, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | ~r1_tarski(A_87, u1_struct_0(A_86)))), inference(resolution, [status(thm)], [c_10, c_307])).
% 2.91/1.41  tff(c_387, plain, (![A_87]: (r1_tarski('#skF_2', k1_tops_1('#skF_1', A_87)) | ~m2_connsp_2(A_87, '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(A_87, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_376])).
% 2.91/1.41  tff(c_458, plain, (![A_94]: (r1_tarski('#skF_2', k1_tops_1('#skF_1', A_94)) | ~m2_connsp_2(A_94, '#skF_1', '#skF_2') | ~r1_tarski(A_94, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_387])).
% 2.91/1.41  tff(c_470, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_142, c_458])).
% 2.91/1.41  tff(c_482, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_470])).
% 2.91/1.41  tff(c_14, plain, (![A_11, B_13]: (r1_tarski(k1_tops_1(A_11, B_13), B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.91/1.41  tff(c_131, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_127, c_14])).
% 2.91/1.41  tff(c_140, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_131])).
% 2.91/1.41  tff(c_4, plain, (![A_3]: (~v1_xboole_0(k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.91/1.41  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k1_zfmisc_1(A_1), k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.41  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.91/1.41  tff(c_46, plain, (![A_38, C_39, B_40]: (m1_subset_1(A_38, C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.91/1.41  tff(c_54, plain, (![A_42, B_43, A_44]: (m1_subset_1(A_42, B_43) | ~r2_hidden(A_42, A_44) | ~r1_tarski(A_44, B_43))), inference(resolution, [status(thm)], [c_10, c_46])).
% 2.91/1.41  tff(c_69, plain, (![A_49, B_50, B_51]: (m1_subset_1(A_49, B_50) | ~r1_tarski(B_51, B_50) | v1_xboole_0(B_51) | ~m1_subset_1(A_49, B_51))), inference(resolution, [status(thm)], [c_6, c_54])).
% 2.91/1.41  tff(c_75, plain, (![A_49, B_2, A_1]: (m1_subset_1(A_49, k1_zfmisc_1(B_2)) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_49, k1_zfmisc_1(A_1)) | ~r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_69])).
% 2.91/1.41  tff(c_85, plain, (![A_52, B_53, A_54]: (m1_subset_1(A_52, k1_zfmisc_1(B_53)) | ~m1_subset_1(A_52, k1_zfmisc_1(A_54)) | ~r1_tarski(A_54, B_53))), inference(negUnitSimplification, [status(thm)], [c_4, c_75])).
% 2.91/1.41  tff(c_90, plain, (![A_6, B_53, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_53)) | ~r1_tarski(B_7, B_53) | ~r1_tarski(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_85])).
% 2.91/1.41  tff(c_153, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1('#skF_3')) | ~r1_tarski(A_6, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_140, c_90])).
% 2.91/1.41  tff(c_498, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_482, c_153])).
% 2.91/1.41  tff(c_511, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_498, c_8])).
% 2.91/1.41  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_511])).
% 2.91/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  Inference rules
% 2.91/1.41  ----------------------
% 2.91/1.41  #Ref     : 0
% 2.91/1.41  #Sup     : 115
% 2.91/1.41  #Fact    : 0
% 2.91/1.41  #Define  : 0
% 2.91/1.41  #Split   : 4
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.42  Ordering : KBO
% 2.91/1.42  
% 2.91/1.42  Simplification rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Subsume      : 7
% 2.91/1.42  #Demod        : 39
% 2.91/1.42  #Tautology    : 10
% 2.91/1.42  #SimpNegUnit  : 2
% 2.91/1.42  #BackRed      : 0
% 2.91/1.42  
% 2.91/1.42  #Partial instantiations: 0
% 2.91/1.42  #Strategies tried      : 1
% 2.91/1.42  
% 2.91/1.42  Timing (in seconds)
% 2.91/1.42  ----------------------
% 2.91/1.42  Preprocessing        : 0.29
% 2.91/1.42  Parsing              : 0.17
% 2.91/1.42  CNF conversion       : 0.02
% 2.91/1.42  Main loop            : 0.36
% 2.91/1.42  Inferencing          : 0.14
% 2.91/1.42  Reduction            : 0.10
% 2.91/1.42  Demodulation         : 0.07
% 2.91/1.42  BG Simplification    : 0.02
% 2.91/1.42  Subsumption          : 0.08
% 2.91/1.42  Abstraction          : 0.01
% 2.91/1.42  MUC search           : 0.00
% 2.91/1.42  Cooper               : 0.00
% 2.91/1.42  Total                : 0.69
% 2.91/1.42  Index Insertion      : 0.00
% 2.91/1.42  Index Deletion       : 0.00
% 2.91/1.42  Index Matching       : 0.00
% 2.91/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
