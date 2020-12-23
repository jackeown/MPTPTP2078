%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:14 EST 2020

% Result     : Theorem 17.31s
% Output     : CNFRefutation 17.50s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 489 expanded)
%              Number of leaves         :   59 ( 189 expanded)
%              Depth                    :   19
%              Number of atoms          :  285 ( 975 expanded)
%              Number of equality atoms :  115 ( 290 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_156,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_99,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_87,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_75,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_105,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_149,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_142,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_102,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_100,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_36094,plain,(
    ! [A_922,B_923,C_924] :
      ( k7_subset_1(A_922,B_923,C_924) = k4_xboole_0(B_923,C_924)
      | ~ m1_subset_1(B_923,k1_zfmisc_1(A_922)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36115,plain,(
    ! [C_924] : k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',C_924) = k4_xboole_0('#skF_7',C_924) ),
    inference(resolution,[status(thm)],[c_100,c_36094])).

tff(c_40039,plain,(
    ! [A_1062,B_1063] :
      ( k7_subset_1(u1_struct_0(A_1062),B_1063,k2_tops_1(A_1062,B_1063)) = k1_tops_1(A_1062,B_1063)
      | ~ m1_subset_1(B_1063,k1_zfmisc_1(u1_struct_0(A_1062)))
      | ~ l1_pre_topc(A_1062) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40067,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_40039])).

tff(c_40086,plain,(
    k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_36115,c_40067])).

tff(c_76,plain,(
    ! [A_50,B_51] : k6_subset_1(A_50,B_51) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_70,plain,(
    ! [A_43,B_44] : m1_subset_1(k6_subset_1(A_43,B_44),k1_zfmisc_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_113,plain,(
    ! [A_43,B_44] : m1_subset_1(k4_xboole_0(A_43,B_44),k1_zfmisc_1(A_43)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70])).

tff(c_35374,plain,(
    ! [A_889,B_890] :
      ( k4_xboole_0(A_889,B_890) = k3_subset_1(A_889,B_890)
      | ~ m1_subset_1(B_890,k1_zfmisc_1(A_889)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_35389,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_subset_1(A_43,k4_xboole_0(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_113,c_35374])).

tff(c_40111,plain,(
    k3_subset_1('#skF_7',k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7'))) = k4_xboole_0('#skF_7',k1_tops_1('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40086,c_35389])).

tff(c_40157,plain,(
    k4_xboole_0('#skF_7',k1_tops_1('#skF_6','#skF_7')) = k3_subset_1('#skF_7',k1_tops_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40086,c_40111])).

tff(c_106,plain,
    ( k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_tops_1('#skF_6','#skF_7')) != k2_tops_1('#skF_6','#skF_7')
    | ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_243,plain,(
    ~ v4_pre_topc('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_104,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3614,plain,(
    ! [B_266,A_267] :
      ( v4_pre_topc(B_266,A_267)
      | k2_pre_topc(A_267,B_266) != B_266
      | ~ v2_pre_topc(A_267)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3643,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | k2_pre_topc('#skF_6','#skF_7') != '#skF_7'
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_3614])).

tff(c_3655,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | k2_pre_topc('#skF_6','#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_104,c_3643])).

tff(c_3656,plain,(
    k2_pre_topc('#skF_6','#skF_7') != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_3655])).

tff(c_1901,plain,(
    ! [A_204,B_205,C_206] :
      ( k7_subset_1(A_204,B_205,C_206) = k4_xboole_0(B_205,C_206)
      | ~ m1_subset_1(B_205,k1_zfmisc_1(A_204)) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1983,plain,(
    ! [C_210] : k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',C_210) = k4_xboole_0('#skF_7',C_210) ),
    inference(resolution,[status(thm)],[c_100,c_1901])).

tff(c_112,plain,
    ( v4_pre_topc('#skF_7','#skF_6')
    | k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_tops_1('#skF_6','#skF_7')) = k2_tops_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_148,plain,(
    k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_tops_1('#skF_6','#skF_7')) = k2_tops_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_1989,plain,(
    k4_xboole_0('#skF_7',k1_tops_1('#skF_6','#skF_7')) = k2_tops_1('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_148])).

tff(c_46,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    ! [B_36,A_35] : k2_tarski(B_36,A_35) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_208,plain,(
    ! [A_93,B_94] : k1_setfam_1(k2_tarski(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_244,plain,(
    ! [B_99,A_100] : k1_setfam_1(k2_tarski(B_99,A_100)) = k3_xboole_0(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_208])).

tff(c_80,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_250,plain,(
    ! [B_99,A_100] : k3_xboole_0(B_99,A_100) = k3_xboole_0(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_80])).

tff(c_50,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ! [A_25,B_26,C_27] :
      ( r1_tarski(k4_xboole_0(A_25,B_26),C_27)
      | ~ r1_tarski(A_25,k2_xboole_0(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_816,plain,(
    ! [C_147,B_148,A_149] :
      ( r2_hidden(C_147,B_148)
      | ~ r2_hidden(C_147,A_149)
      | ~ r1_tarski(A_149,B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_819,plain,(
    ! [A_1,B_2,B_148] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_148)
      | ~ r1_tarski(A_1,B_148)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_816])).

tff(c_52,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_563,plain,(
    ! [A_122,B_123] :
      ( r2_hidden('#skF_1'(A_122,B_123),A_122)
      | r1_tarski(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [D_17,B_13,A_12] :
      ( ~ r2_hidden(D_17,B_13)
      | ~ r2_hidden(D_17,k4_xboole_0(A_12,B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10355,plain,(
    ! [A_453,B_454,B_455] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_453,B_454),B_455),B_454)
      | r1_tarski(k4_xboole_0(A_453,B_454),B_455) ) ),
    inference(resolution,[status(thm)],[c_563,c_28])).

tff(c_10424,plain,(
    ! [A_24,B_455] :
      ( ~ r2_hidden('#skF_1'(A_24,B_455),k1_xboole_0)
      | r1_tarski(k4_xboole_0(A_24,k1_xboole_0),B_455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10355])).

tff(c_10447,plain,(
    ! [A_456,B_457] :
      ( ~ r2_hidden('#skF_1'(A_456,B_457),k1_xboole_0)
      | r1_tarski(A_456,B_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_10424])).

tff(c_10471,plain,(
    ! [A_458,B_459] :
      ( ~ r1_tarski(A_458,k1_xboole_0)
      | r1_tarski(A_458,B_459) ) ),
    inference(resolution,[status(thm)],[c_819,c_10447])).

tff(c_10501,plain,(
    ! [A_25,B_26,B_459] :
      ( r1_tarski(k4_xboole_0(A_25,B_26),B_459)
      | ~ r1_tarski(A_25,k2_xboole_0(B_26,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_54,c_10471])).

tff(c_10536,plain,(
    ! [A_460,B_461,B_462] :
      ( r1_tarski(k4_xboole_0(A_460,B_461),B_462)
      | ~ r1_tarski(A_460,B_461) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10501])).

tff(c_522,plain,(
    ! [D_115,B_116,A_117] :
      ( ~ r2_hidden(D_115,B_116)
      | ~ r2_hidden(D_115,k4_xboole_0(A_117,B_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_528,plain,(
    ! [D_115,A_24] :
      ( ~ r2_hidden(D_115,k1_xboole_0)
      | ~ r2_hidden(D_115,A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_522])).

tff(c_802,plain,(
    ! [B_144,A_145] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_144),A_145)
      | r1_tarski(k1_xboole_0,B_144) ) ),
    inference(resolution,[status(thm)],[c_563,c_528])).

tff(c_807,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_802])).

tff(c_84,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(A_57,k1_zfmisc_1(B_58))
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1078,plain,(
    ! [A_164,B_165] :
      ( k4_xboole_0(A_164,B_165) = k3_subset_1(A_164,B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_164)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2213,plain,(
    ! [B_219,A_220] :
      ( k4_xboole_0(B_219,A_220) = k3_subset_1(B_219,A_220)
      | ~ r1_tarski(A_220,B_219) ) ),
    inference(resolution,[status(thm)],[c_84,c_1078])).

tff(c_2249,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_subset_1(B_2,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_807,c_2213])).

tff(c_2280,plain,(
    ! [B_221] : k3_subset_1(B_221,k1_xboole_0) = B_221 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2249])).

tff(c_933,plain,(
    ! [A_154,B_155] :
      ( k3_subset_1(A_154,k3_subset_1(A_154,B_155)) = B_155
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_942,plain,(
    ! [B_58,A_57] :
      ( k3_subset_1(B_58,k3_subset_1(B_58,A_57)) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_84,c_933])).

tff(c_2325,plain,(
    ! [B_221] :
      ( k3_subset_1(B_221,B_221) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,B_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2280,c_942])).

tff(c_2343,plain,(
    ! [B_221] : k3_subset_1(B_221,B_221) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_2325])).

tff(c_144,plain,(
    ! [A_82,B_83] : m1_subset_1(k4_xboole_0(A_82,B_83),k1_zfmisc_1(A_82)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_70])).

tff(c_147,plain,(
    ! [A_24] : m1_subset_1(A_24,k1_zfmisc_1(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_144])).

tff(c_1092,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k3_subset_1(A_24,A_24) ),
    inference(resolution,[status(thm)],[c_147,c_1078])).

tff(c_2374,plain,(
    ! [A_24] : k4_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2343,c_1092])).

tff(c_42,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden('#skF_4'(A_12,B_13,C_14),A_12)
      | r2_hidden('#skF_5'(A_12,B_13,C_14),C_14)
      | k4_xboole_0(A_12,B_13) = C_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4425,plain,(
    ! [A_301,B_302,C_303] :
      ( ~ r2_hidden('#skF_4'(A_301,B_302,C_303),B_302)
      | r2_hidden('#skF_5'(A_301,B_302,C_303),C_303)
      | k4_xboole_0(A_301,B_302) = C_303 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4428,plain,(
    ! [A_12,C_14] :
      ( r2_hidden('#skF_5'(A_12,A_12,C_14),C_14)
      | k4_xboole_0(A_12,A_12) = C_14 ) ),
    inference(resolution,[status(thm)],[c_42,c_4425])).

tff(c_4443,plain,(
    ! [A_304,C_305] :
      ( r2_hidden('#skF_5'(A_304,A_304,C_305),C_305)
      | k1_xboole_0 = C_305 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2374,c_4428])).

tff(c_86,plain,(
    ! [B_60,A_59] :
      ( ~ r1_tarski(B_60,A_59)
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4495,plain,(
    ! [C_305,A_304] :
      ( ~ r1_tarski(C_305,'#skF_5'(A_304,A_304,C_305))
      | k1_xboole_0 = C_305 ) ),
    inference(resolution,[status(thm)],[c_4443,c_86])).

tff(c_10641,plain,(
    ! [A_463,B_464] :
      ( k4_xboole_0(A_463,B_464) = k1_xboole_0
      | ~ r1_tarski(A_463,B_464) ) ),
    inference(resolution,[status(thm)],[c_10536,c_4495])).

tff(c_11388,plain,(
    ! [A_468,B_469] : k4_xboole_0(k4_xboole_0(A_468,B_469),A_468) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_10641])).

tff(c_58,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_11461,plain,(
    ! [A_468,B_469] : k2_xboole_0(k3_xboole_0(k4_xboole_0(A_468,B_469),A_468),k1_xboole_0) = k4_xboole_0(A_468,B_469) ),
    inference(superposition,[status(thm),theory(equality)],[c_11388,c_58])).

tff(c_33177,plain,(
    ! [A_782,B_783] : k3_xboole_0(A_782,k4_xboole_0(A_782,B_783)) = k4_xboole_0(A_782,B_783) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_250,c_11461])).

tff(c_228,plain,(
    ! [A_97,B_98] : k3_tarski(k2_tarski(A_97,B_98)) = k2_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_412,plain,(
    ! [A_108,B_109] : k3_tarski(k2_tarski(A_108,B_109)) = k2_xboole_0(B_109,A_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_228])).

tff(c_64,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_418,plain,(
    ! [B_109,A_108] : k2_xboole_0(B_109,A_108) = k2_xboole_0(A_108,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_64])).

tff(c_618,plain,(
    ! [A_132,B_133] : k2_xboole_0(A_132,k2_xboole_0(A_132,B_133)) = k2_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_637,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = k2_xboole_0(k3_xboole_0(A_31,B_32),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_618])).

tff(c_659,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = A_31 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_418,c_637])).

tff(c_33641,plain,(
    ! [A_784,B_785] : k2_xboole_0(A_784,k4_xboole_0(A_784,B_785)) = A_784 ),
    inference(superposition,[status(thm),theory(equality)],[c_33177,c_659])).

tff(c_34011,plain,(
    k2_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_1989,c_33641])).

tff(c_5025,plain,(
    ! [A_322,B_323] :
      ( k4_subset_1(u1_struct_0(A_322),B_323,k2_tops_1(A_322,B_323)) = k2_pre_topc(A_322,B_323)
      | ~ m1_subset_1(B_323,k1_zfmisc_1(u1_struct_0(A_322)))
      | ~ l1_pre_topc(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_5051,plain,
    ( k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k2_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_5025])).

tff(c_5067,plain,(
    k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k2_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_5051])).

tff(c_1094,plain,(
    k4_xboole_0(u1_struct_0('#skF_6'),'#skF_7') = k3_subset_1(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_1078])).

tff(c_1201,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_113])).

tff(c_4800,plain,(
    ! [A_317,B_318] :
      ( k2_tops_1(A_317,k3_subset_1(u1_struct_0(A_317),B_318)) = k2_tops_1(A_317,B_318)
      | ~ m1_subset_1(B_318,k1_zfmisc_1(u1_struct_0(A_317)))
      | ~ l1_pre_topc(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4821,plain,
    ( k2_tops_1('#skF_6',k3_subset_1(u1_struct_0('#skF_6'),'#skF_7')) = k2_tops_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_4800])).

tff(c_4835,plain,(
    k2_tops_1('#skF_6',k3_subset_1(u1_struct_0('#skF_6'),'#skF_7')) = k2_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_4821])).

tff(c_92,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k2_tops_1(A_64,B_65),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_4945,plain,
    ( m1_subset_1(k2_tops_1('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4835,c_92])).

tff(c_4949,plain,(
    m1_subset_1(k2_tops_1('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_1201,c_4945])).

tff(c_82,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4993,plain,(
    r1_tarski(k2_tops_1('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4949,c_82])).

tff(c_2689,plain,(
    ! [A_231,B_232,C_233] :
      ( k4_subset_1(A_231,B_232,C_233) = k2_xboole_0(B_232,C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(A_231))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(A_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_14200,plain,(
    ! [B_498,B_499,A_500] :
      ( k4_subset_1(B_498,B_499,A_500) = k2_xboole_0(B_499,A_500)
      | ~ m1_subset_1(B_499,k1_zfmisc_1(B_498))
      | ~ r1_tarski(A_500,B_498) ) ),
    inference(resolution,[status(thm)],[c_84,c_2689])).

tff(c_14274,plain,(
    ! [A_501] :
      ( k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',A_501) = k2_xboole_0('#skF_7',A_501)
      | ~ r1_tarski(A_501,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_100,c_14200])).

tff(c_14305,plain,(
    k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4993,c_14274])).

tff(c_14360,plain,(
    k2_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k2_pre_topc('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5067,c_14305])).

tff(c_34130,plain,(
    k2_pre_topc('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34011,c_14360])).

tff(c_34132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3656,c_34130])).

tff(c_34133,plain,(
    k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_tops_1('#skF_6','#skF_7')) != k2_tops_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_34358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34133,c_148])).

tff(c_34359,plain,(
    v4_pre_topc('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_34441,plain,(
    k7_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_tops_1('#skF_6','#skF_7')) != k2_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34359,c_106])).

tff(c_36125,plain,(
    k4_xboole_0('#skF_7',k1_tops_1('#skF_6','#skF_7')) != k2_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36115,c_34441])).

tff(c_40515,plain,(
    k3_subset_1('#skF_7',k1_tops_1('#skF_6','#skF_7')) != k2_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40157,c_36125])).

tff(c_36870,plain,(
    ! [A_952,B_953] :
      ( k2_pre_topc(A_952,B_953) = B_953
      | ~ v4_pre_topc(B_953,A_952)
      | ~ m1_subset_1(B_953,k1_zfmisc_1(u1_struct_0(A_952)))
      | ~ l1_pre_topc(A_952) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36899,plain,
    ( k2_pre_topc('#skF_6','#skF_7') = '#skF_7'
    | ~ v4_pre_topc('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_36870])).

tff(c_36911,plain,(
    k2_pre_topc('#skF_6','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_34359,c_36899])).

tff(c_40286,plain,(
    ! [A_1066,B_1067] :
      ( k4_subset_1(u1_struct_0(A_1066),B_1067,k2_tops_1(A_1066,B_1067)) = k2_pre_topc(A_1066,B_1067)
      | ~ m1_subset_1(B_1067,k1_zfmisc_1(u1_struct_0(A_1066)))
      | ~ l1_pre_topc(A_1066) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40314,plain,
    ( k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k2_pre_topc('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_40286])).

tff(c_40331,plain,(
    k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_36911,c_40314])).

tff(c_35390,plain,(
    k4_xboole_0(u1_struct_0('#skF_6'),'#skF_7') = k3_subset_1(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_35374])).

tff(c_35466,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35390,c_113])).

tff(c_37643,plain,(
    ! [A_984,B_985] :
      ( k2_tops_1(A_984,k3_subset_1(u1_struct_0(A_984),B_985)) = k2_tops_1(A_984,B_985)
      | ~ m1_subset_1(B_985,k1_zfmisc_1(u1_struct_0(A_984)))
      | ~ l1_pre_topc(A_984) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_37664,plain,
    ( k2_tops_1('#skF_6',k3_subset_1(u1_struct_0('#skF_6'),'#skF_7')) = k2_tops_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_37643])).

tff(c_37678,plain,(
    k2_tops_1('#skF_6',k3_subset_1(u1_struct_0('#skF_6'),'#skF_7')) = k2_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_37664])).

tff(c_37682,plain,
    ( m1_subset_1(k2_tops_1('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'),'#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_37678,c_92])).

tff(c_37686,plain,(
    m1_subset_1(k2_tops_1('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_35466,c_37682])).

tff(c_37724,plain,(
    r1_tarski(k2_tops_1('#skF_6','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_37686,c_82])).

tff(c_37133,plain,(
    ! [A_963,B_964,C_965] :
      ( k4_subset_1(A_963,B_964,C_965) = k2_xboole_0(B_964,C_965)
      | ~ m1_subset_1(C_965,k1_zfmisc_1(A_963))
      | ~ m1_subset_1(B_964,k1_zfmisc_1(A_963)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_51203,plain,(
    ! [B_1271,B_1272,A_1273] :
      ( k4_subset_1(B_1271,B_1272,A_1273) = k2_xboole_0(B_1272,A_1273)
      | ~ m1_subset_1(B_1272,k1_zfmisc_1(B_1271))
      | ~ r1_tarski(A_1273,B_1271) ) ),
    inference(resolution,[status(thm)],[c_84,c_37133])).

tff(c_51411,plain,(
    ! [A_1277] :
      ( k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',A_1277) = k2_xboole_0('#skF_7',A_1277)
      | ~ r1_tarski(A_1277,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_100,c_51203])).

tff(c_51458,plain,(
    k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k2_tops_1('#skF_6','#skF_7')) = k2_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_37724,c_51411])).

tff(c_51517,plain,(
    k2_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40331,c_51458])).

tff(c_35029,plain,(
    ! [A_869,B_870,C_871] :
      ( r1_tarski(A_869,k2_xboole_0(B_870,C_871))
      | ~ r1_tarski(k4_xboole_0(A_869,B_870),C_871) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_35046,plain,(
    ! [A_22,B_23] : r1_tarski(A_22,k2_xboole_0(B_23,A_22)) ),
    inference(resolution,[status(thm)],[c_50,c_35029])).

tff(c_51686,plain,(
    r1_tarski(k2_tops_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_51517,c_35046])).

tff(c_36319,plain,(
    ! [B_935,A_936] :
      ( k4_xboole_0(B_935,A_936) = k3_subset_1(B_935,A_936)
      | ~ r1_tarski(A_936,B_935) ) ),
    inference(resolution,[status(thm)],[c_84,c_35374])).

tff(c_36372,plain,(
    ! [B_23,A_22] : k4_xboole_0(k2_xboole_0(B_23,A_22),A_22) = k3_subset_1(k2_xboole_0(B_23,A_22),A_22) ),
    inference(resolution,[status(thm)],[c_35046,c_36319])).

tff(c_51659,plain,(
    k3_subset_1(k2_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')),k2_tops_1('#skF_6','#skF_7')) = k4_xboole_0('#skF_7',k2_tops_1('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_51517,c_36372])).

tff(c_51728,plain,(
    k3_subset_1('#skF_7',k2_tops_1('#skF_6','#skF_7')) = k1_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51517,c_40086,c_51659])).

tff(c_35161,plain,(
    ! [A_880,B_881] :
      ( k3_subset_1(A_880,k3_subset_1(A_880,B_881)) = B_881
      | ~ m1_subset_1(B_881,k1_zfmisc_1(A_880)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_35170,plain,(
    ! [B_58,A_57] :
      ( k3_subset_1(B_58,k3_subset_1(B_58,A_57)) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_84,c_35161])).

tff(c_59932,plain,
    ( k3_subset_1('#skF_7',k1_tops_1('#skF_6','#skF_7')) = k2_tops_1('#skF_6','#skF_7')
    | ~ r1_tarski(k2_tops_1('#skF_6','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_51728,c_35170])).

tff(c_59943,plain,(
    k3_subset_1('#skF_7',k1_tops_1('#skF_6','#skF_7')) = k2_tops_1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51686,c_59932])).

tff(c_59945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40515,c_59943])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:24:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.31/9.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.31/9.59  
% 17.31/9.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.31/9.59  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3 > #skF_1
% 17.31/9.59  
% 17.31/9.59  %Foreground sorts:
% 17.31/9.59  
% 17.31/9.59  
% 17.31/9.59  %Background operators:
% 17.31/9.59  
% 17.31/9.59  
% 17.31/9.59  %Foreground operators:
% 17.31/9.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.31/9.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.31/9.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.31/9.59  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 17.31/9.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.31/9.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.31/9.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 17.31/9.59  tff('#skF_7', type, '#skF_7': $i).
% 17.31/9.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.31/9.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.31/9.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.31/9.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.31/9.59  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 17.31/9.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 17.31/9.59  tff('#skF_6', type, '#skF_6': $i).
% 17.31/9.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.31/9.59  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 17.31/9.59  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 17.31/9.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.31/9.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.31/9.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 17.31/9.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.31/9.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.31/9.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.31/9.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.31/9.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 17.31/9.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.31/9.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.31/9.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.31/9.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.31/9.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 17.31/9.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.31/9.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 17.31/9.59  
% 17.50/9.62  tff(f_168, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 17.50/9.62  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 17.50/9.62  tff(f_156, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 17.50/9.62  tff(f_99, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 17.50/9.62  tff(f_87, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 17.50/9.62  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 17.50/9.62  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 17.50/9.62  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 17.50/9.62  tff(f_75, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 17.50/9.62  tff(f_105, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 17.50/9.62  tff(f_59, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 17.50/9.62  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 17.50/9.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.50/9.62  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 17.50/9.62  tff(f_51, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.50/9.62  tff(f_109, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 17.50/9.62  tff(f_91, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 17.50/9.62  tff(f_114, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 17.50/9.62  tff(f_71, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 17.50/9.62  tff(f_77, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 17.50/9.62  tff(f_73, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 17.50/9.62  tff(f_149, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 17.50/9.62  tff(f_142, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 17.50/9.62  tff(f_135, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 17.50/9.62  tff(f_97, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 17.50/9.62  tff(f_69, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 17.50/9.62  tff(c_102, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 17.50/9.62  tff(c_100, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 17.50/9.62  tff(c_36094, plain, (![A_922, B_923, C_924]: (k7_subset_1(A_922, B_923, C_924)=k4_xboole_0(B_923, C_924) | ~m1_subset_1(B_923, k1_zfmisc_1(A_922)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.50/9.62  tff(c_36115, plain, (![C_924]: (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', C_924)=k4_xboole_0('#skF_7', C_924))), inference(resolution, [status(thm)], [c_100, c_36094])).
% 17.50/9.62  tff(c_40039, plain, (![A_1062, B_1063]: (k7_subset_1(u1_struct_0(A_1062), B_1063, k2_tops_1(A_1062, B_1063))=k1_tops_1(A_1062, B_1063) | ~m1_subset_1(B_1063, k1_zfmisc_1(u1_struct_0(A_1062))) | ~l1_pre_topc(A_1062))), inference(cnfTransformation, [status(thm)], [f_156])).
% 17.50/9.62  tff(c_40067, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_100, c_40039])).
% 17.50/9.62  tff(c_40086, plain, (k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_36115, c_40067])).
% 17.50/9.62  tff(c_76, plain, (![A_50, B_51]: (k6_subset_1(A_50, B_51)=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_99])).
% 17.50/9.62  tff(c_70, plain, (![A_43, B_44]: (m1_subset_1(k6_subset_1(A_43, B_44), k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 17.50/9.62  tff(c_113, plain, (![A_43, B_44]: (m1_subset_1(k4_xboole_0(A_43, B_44), k1_zfmisc_1(A_43)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70])).
% 17.50/9.62  tff(c_35374, plain, (![A_889, B_890]: (k4_xboole_0(A_889, B_890)=k3_subset_1(A_889, B_890) | ~m1_subset_1(B_890, k1_zfmisc_1(A_889)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.50/9.62  tff(c_35389, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_subset_1(A_43, k4_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_113, c_35374])).
% 17.50/9.62  tff(c_40111, plain, (k3_subset_1('#skF_7', k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7')))=k4_xboole_0('#skF_7', k1_tops_1('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_40086, c_35389])).
% 17.50/9.62  tff(c_40157, plain, (k4_xboole_0('#skF_7', k1_tops_1('#skF_6', '#skF_7'))=k3_subset_1('#skF_7', k1_tops_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_40086, c_40111])).
% 17.50/9.62  tff(c_106, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k1_tops_1('#skF_6', '#skF_7'))!=k2_tops_1('#skF_6', '#skF_7') | ~v4_pre_topc('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 17.50/9.62  tff(c_243, plain, (~v4_pre_topc('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_106])).
% 17.50/9.62  tff(c_104, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_168])).
% 17.50/9.62  tff(c_3614, plain, (![B_266, A_267]: (v4_pre_topc(B_266, A_267) | k2_pre_topc(A_267, B_266)!=B_266 | ~v2_pre_topc(A_267) | ~m1_subset_1(B_266, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.50/9.62  tff(c_3643, plain, (v4_pre_topc('#skF_7', '#skF_6') | k2_pre_topc('#skF_6', '#skF_7')!='#skF_7' | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_100, c_3614])).
% 17.50/9.62  tff(c_3655, plain, (v4_pre_topc('#skF_7', '#skF_6') | k2_pre_topc('#skF_6', '#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_104, c_3643])).
% 17.50/9.62  tff(c_3656, plain, (k2_pre_topc('#skF_6', '#skF_7')!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_243, c_3655])).
% 17.50/9.62  tff(c_1901, plain, (![A_204, B_205, C_206]: (k7_subset_1(A_204, B_205, C_206)=k4_xboole_0(B_205, C_206) | ~m1_subset_1(B_205, k1_zfmisc_1(A_204)))), inference(cnfTransformation, [status(thm)], [f_103])).
% 17.50/9.62  tff(c_1983, plain, (![C_210]: (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', C_210)=k4_xboole_0('#skF_7', C_210))), inference(resolution, [status(thm)], [c_100, c_1901])).
% 17.50/9.62  tff(c_112, plain, (v4_pre_topc('#skF_7', '#skF_6') | k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k1_tops_1('#skF_6', '#skF_7'))=k2_tops_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_168])).
% 17.50/9.62  tff(c_148, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k1_tops_1('#skF_6', '#skF_7'))=k2_tops_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_112])).
% 17.50/9.62  tff(c_1989, plain, (k4_xboole_0('#skF_7', k1_tops_1('#skF_6', '#skF_7'))=k2_tops_1('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1983, c_148])).
% 17.50/9.62  tff(c_46, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_55])).
% 17.50/9.62  tff(c_62, plain, (![B_36, A_35]: (k2_tarski(B_36, A_35)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.50/9.62  tff(c_208, plain, (![A_93, B_94]: (k1_setfam_1(k2_tarski(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.50/9.62  tff(c_244, plain, (![B_99, A_100]: (k1_setfam_1(k2_tarski(B_99, A_100))=k3_xboole_0(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_62, c_208])).
% 17.50/9.62  tff(c_80, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_105])).
% 17.50/9.62  tff(c_250, plain, (![B_99, A_100]: (k3_xboole_0(B_99, A_100)=k3_xboole_0(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_244, c_80])).
% 17.50/9.62  tff(c_50, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.50/9.62  tff(c_54, plain, (![A_25, B_26, C_27]: (r1_tarski(k4_xboole_0(A_25, B_26), C_27) | ~r1_tarski(A_25, k2_xboole_0(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 17.50/9.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.50/9.62  tff(c_816, plain, (![C_147, B_148, A_149]: (r2_hidden(C_147, B_148) | ~r2_hidden(C_147, A_149) | ~r1_tarski(A_149, B_148))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.50/9.62  tff(c_819, plain, (![A_1, B_2, B_148]: (r2_hidden('#skF_1'(A_1, B_2), B_148) | ~r1_tarski(A_1, B_148) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_816])).
% 17.50/9.62  tff(c_52, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_61])).
% 17.50/9.62  tff(c_563, plain, (![A_122, B_123]: (r2_hidden('#skF_1'(A_122, B_123), A_122) | r1_tarski(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.50/9.62  tff(c_28, plain, (![D_17, B_13, A_12]: (~r2_hidden(D_17, B_13) | ~r2_hidden(D_17, k4_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.50/9.62  tff(c_10355, plain, (![A_453, B_454, B_455]: (~r2_hidden('#skF_1'(k4_xboole_0(A_453, B_454), B_455), B_454) | r1_tarski(k4_xboole_0(A_453, B_454), B_455))), inference(resolution, [status(thm)], [c_563, c_28])).
% 17.50/9.62  tff(c_10424, plain, (![A_24, B_455]: (~r2_hidden('#skF_1'(A_24, B_455), k1_xboole_0) | r1_tarski(k4_xboole_0(A_24, k1_xboole_0), B_455))), inference(superposition, [status(thm), theory('equality')], [c_52, c_10355])).
% 17.50/9.62  tff(c_10447, plain, (![A_456, B_457]: (~r2_hidden('#skF_1'(A_456, B_457), k1_xboole_0) | r1_tarski(A_456, B_457))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_10424])).
% 17.50/9.62  tff(c_10471, plain, (![A_458, B_459]: (~r1_tarski(A_458, k1_xboole_0) | r1_tarski(A_458, B_459))), inference(resolution, [status(thm)], [c_819, c_10447])).
% 17.50/9.62  tff(c_10501, plain, (![A_25, B_26, B_459]: (r1_tarski(k4_xboole_0(A_25, B_26), B_459) | ~r1_tarski(A_25, k2_xboole_0(B_26, k1_xboole_0)))), inference(resolution, [status(thm)], [c_54, c_10471])).
% 17.50/9.62  tff(c_10536, plain, (![A_460, B_461, B_462]: (r1_tarski(k4_xboole_0(A_460, B_461), B_462) | ~r1_tarski(A_460, B_461))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10501])).
% 17.50/9.62  tff(c_522, plain, (![D_115, B_116, A_117]: (~r2_hidden(D_115, B_116) | ~r2_hidden(D_115, k4_xboole_0(A_117, B_116)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.50/9.62  tff(c_528, plain, (![D_115, A_24]: (~r2_hidden(D_115, k1_xboole_0) | ~r2_hidden(D_115, A_24))), inference(superposition, [status(thm), theory('equality')], [c_52, c_522])).
% 17.50/9.62  tff(c_802, plain, (![B_144, A_145]: (~r2_hidden('#skF_1'(k1_xboole_0, B_144), A_145) | r1_tarski(k1_xboole_0, B_144))), inference(resolution, [status(thm)], [c_563, c_528])).
% 17.50/9.62  tff(c_807, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_802])).
% 17.50/9.62  tff(c_84, plain, (![A_57, B_58]: (m1_subset_1(A_57, k1_zfmisc_1(B_58)) | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_109])).
% 17.50/9.62  tff(c_1078, plain, (![A_164, B_165]: (k4_xboole_0(A_164, B_165)=k3_subset_1(A_164, B_165) | ~m1_subset_1(B_165, k1_zfmisc_1(A_164)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 17.50/9.62  tff(c_2213, plain, (![B_219, A_220]: (k4_xboole_0(B_219, A_220)=k3_subset_1(B_219, A_220) | ~r1_tarski(A_220, B_219))), inference(resolution, [status(thm)], [c_84, c_1078])).
% 17.50/9.62  tff(c_2249, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_subset_1(B_2, k1_xboole_0))), inference(resolution, [status(thm)], [c_807, c_2213])).
% 17.50/9.62  tff(c_2280, plain, (![B_221]: (k3_subset_1(B_221, k1_xboole_0)=B_221)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2249])).
% 17.50/9.62  tff(c_933, plain, (![A_154, B_155]: (k3_subset_1(A_154, k3_subset_1(A_154, B_155))=B_155 | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 17.50/9.62  tff(c_942, plain, (![B_58, A_57]: (k3_subset_1(B_58, k3_subset_1(B_58, A_57))=A_57 | ~r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_84, c_933])).
% 17.50/9.62  tff(c_2325, plain, (![B_221]: (k3_subset_1(B_221, B_221)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, B_221))), inference(superposition, [status(thm), theory('equality')], [c_2280, c_942])).
% 17.50/9.62  tff(c_2343, plain, (![B_221]: (k3_subset_1(B_221, B_221)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_807, c_2325])).
% 17.50/9.62  tff(c_144, plain, (![A_82, B_83]: (m1_subset_1(k4_xboole_0(A_82, B_83), k1_zfmisc_1(A_82)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_70])).
% 17.50/9.62  tff(c_147, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_144])).
% 17.50/9.62  tff(c_1092, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k3_subset_1(A_24, A_24))), inference(resolution, [status(thm)], [c_147, c_1078])).
% 17.50/9.62  tff(c_2374, plain, (![A_24]: (k4_xboole_0(A_24, A_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2343, c_1092])).
% 17.50/9.62  tff(c_42, plain, (![A_12, B_13, C_14]: (r2_hidden('#skF_4'(A_12, B_13, C_14), A_12) | r2_hidden('#skF_5'(A_12, B_13, C_14), C_14) | k4_xboole_0(A_12, B_13)=C_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.50/9.62  tff(c_4425, plain, (![A_301, B_302, C_303]: (~r2_hidden('#skF_4'(A_301, B_302, C_303), B_302) | r2_hidden('#skF_5'(A_301, B_302, C_303), C_303) | k4_xboole_0(A_301, B_302)=C_303)), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.50/9.62  tff(c_4428, plain, (![A_12, C_14]: (r2_hidden('#skF_5'(A_12, A_12, C_14), C_14) | k4_xboole_0(A_12, A_12)=C_14)), inference(resolution, [status(thm)], [c_42, c_4425])).
% 17.50/9.62  tff(c_4443, plain, (![A_304, C_305]: (r2_hidden('#skF_5'(A_304, A_304, C_305), C_305) | k1_xboole_0=C_305)), inference(demodulation, [status(thm), theory('equality')], [c_2374, c_4428])).
% 17.50/9.62  tff(c_86, plain, (![B_60, A_59]: (~r1_tarski(B_60, A_59) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_114])).
% 17.50/9.62  tff(c_4495, plain, (![C_305, A_304]: (~r1_tarski(C_305, '#skF_5'(A_304, A_304, C_305)) | k1_xboole_0=C_305)), inference(resolution, [status(thm)], [c_4443, c_86])).
% 17.50/9.62  tff(c_10641, plain, (![A_463, B_464]: (k4_xboole_0(A_463, B_464)=k1_xboole_0 | ~r1_tarski(A_463, B_464))), inference(resolution, [status(thm)], [c_10536, c_4495])).
% 17.50/9.62  tff(c_11388, plain, (![A_468, B_469]: (k4_xboole_0(k4_xboole_0(A_468, B_469), A_468)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_10641])).
% 17.50/9.62  tff(c_58, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.50/9.62  tff(c_11461, plain, (![A_468, B_469]: (k2_xboole_0(k3_xboole_0(k4_xboole_0(A_468, B_469), A_468), k1_xboole_0)=k4_xboole_0(A_468, B_469))), inference(superposition, [status(thm), theory('equality')], [c_11388, c_58])).
% 17.50/9.62  tff(c_33177, plain, (![A_782, B_783]: (k3_xboole_0(A_782, k4_xboole_0(A_782, B_783))=k4_xboole_0(A_782, B_783))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_250, c_11461])).
% 17.50/9.62  tff(c_228, plain, (![A_97, B_98]: (k3_tarski(k2_tarski(A_97, B_98))=k2_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.50/9.62  tff(c_412, plain, (![A_108, B_109]: (k3_tarski(k2_tarski(A_108, B_109))=k2_xboole_0(B_109, A_108))), inference(superposition, [status(thm), theory('equality')], [c_62, c_228])).
% 17.50/9.62  tff(c_64, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_77])).
% 17.50/9.62  tff(c_418, plain, (![B_109, A_108]: (k2_xboole_0(B_109, A_108)=k2_xboole_0(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_412, c_64])).
% 17.50/9.62  tff(c_618, plain, (![A_132, B_133]: (k2_xboole_0(A_132, k2_xboole_0(A_132, B_133))=k2_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.50/9.62  tff(c_637, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=k2_xboole_0(k3_xboole_0(A_31, B_32), A_31))), inference(superposition, [status(thm), theory('equality')], [c_58, c_618])).
% 17.50/9.62  tff(c_659, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k3_xboole_0(A_31, B_32))=A_31)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_418, c_637])).
% 17.50/9.62  tff(c_33641, plain, (![A_784, B_785]: (k2_xboole_0(A_784, k4_xboole_0(A_784, B_785))=A_784)), inference(superposition, [status(thm), theory('equality')], [c_33177, c_659])).
% 17.50/9.62  tff(c_34011, plain, (k2_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_1989, c_33641])).
% 17.50/9.62  tff(c_5025, plain, (![A_322, B_323]: (k4_subset_1(u1_struct_0(A_322), B_323, k2_tops_1(A_322, B_323))=k2_pre_topc(A_322, B_323) | ~m1_subset_1(B_323, k1_zfmisc_1(u1_struct_0(A_322))) | ~l1_pre_topc(A_322))), inference(cnfTransformation, [status(thm)], [f_149])).
% 17.50/9.62  tff(c_5051, plain, (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k2_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_100, c_5025])).
% 17.50/9.62  tff(c_5067, plain, (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k2_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_5051])).
% 17.50/9.62  tff(c_1094, plain, (k4_xboole_0(u1_struct_0('#skF_6'), '#skF_7')=k3_subset_1(u1_struct_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_100, c_1078])).
% 17.50/9.62  tff(c_1201, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_113])).
% 17.50/9.62  tff(c_4800, plain, (![A_317, B_318]: (k2_tops_1(A_317, k3_subset_1(u1_struct_0(A_317), B_318))=k2_tops_1(A_317, B_318) | ~m1_subset_1(B_318, k1_zfmisc_1(u1_struct_0(A_317))) | ~l1_pre_topc(A_317))), inference(cnfTransformation, [status(thm)], [f_142])).
% 17.50/9.62  tff(c_4821, plain, (k2_tops_1('#skF_6', k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'))=k2_tops_1('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_100, c_4800])).
% 17.50/9.62  tff(c_4835, plain, (k2_tops_1('#skF_6', k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'))=k2_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_4821])).
% 17.50/9.62  tff(c_92, plain, (![A_64, B_65]: (m1_subset_1(k2_tops_1(A_64, B_65), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_135])).
% 17.50/9.62  tff(c_4945, plain, (m1_subset_1(k2_tops_1('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4835, c_92])).
% 17.50/9.62  tff(c_4949, plain, (m1_subset_1(k2_tops_1('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_1201, c_4945])).
% 17.50/9.62  tff(c_82, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 17.50/9.62  tff(c_4993, plain, (r1_tarski(k2_tops_1('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_4949, c_82])).
% 17.50/9.62  tff(c_2689, plain, (![A_231, B_232, C_233]: (k4_subset_1(A_231, B_232, C_233)=k2_xboole_0(B_232, C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(A_231)) | ~m1_subset_1(B_232, k1_zfmisc_1(A_231)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.50/9.62  tff(c_14200, plain, (![B_498, B_499, A_500]: (k4_subset_1(B_498, B_499, A_500)=k2_xboole_0(B_499, A_500) | ~m1_subset_1(B_499, k1_zfmisc_1(B_498)) | ~r1_tarski(A_500, B_498))), inference(resolution, [status(thm)], [c_84, c_2689])).
% 17.50/9.62  tff(c_14274, plain, (![A_501]: (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', A_501)=k2_xboole_0('#skF_7', A_501) | ~r1_tarski(A_501, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_100, c_14200])).
% 17.50/9.62  tff(c_14305, plain, (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4993, c_14274])).
% 17.50/9.62  tff(c_14360, plain, (k2_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k2_pre_topc('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5067, c_14305])).
% 17.50/9.62  tff(c_34130, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_34011, c_14360])).
% 17.50/9.62  tff(c_34132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3656, c_34130])).
% 17.50/9.62  tff(c_34133, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k1_tops_1('#skF_6', '#skF_7'))!=k2_tops_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_106])).
% 17.50/9.62  tff(c_34358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34133, c_148])).
% 17.50/9.62  tff(c_34359, plain, (v4_pre_topc('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_112])).
% 17.50/9.62  tff(c_34441, plain, (k7_subset_1(u1_struct_0('#skF_6'), '#skF_7', k1_tops_1('#skF_6', '#skF_7'))!=k2_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34359, c_106])).
% 17.50/9.62  tff(c_36125, plain, (k4_xboole_0('#skF_7', k1_tops_1('#skF_6', '#skF_7'))!=k2_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36115, c_34441])).
% 17.50/9.62  tff(c_40515, plain, (k3_subset_1('#skF_7', k1_tops_1('#skF_6', '#skF_7'))!=k2_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40157, c_36125])).
% 17.50/9.62  tff(c_36870, plain, (![A_952, B_953]: (k2_pre_topc(A_952, B_953)=B_953 | ~v4_pre_topc(B_953, A_952) | ~m1_subset_1(B_953, k1_zfmisc_1(u1_struct_0(A_952))) | ~l1_pre_topc(A_952))), inference(cnfTransformation, [status(thm)], [f_129])).
% 17.50/9.62  tff(c_36899, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7' | ~v4_pre_topc('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_100, c_36870])).
% 17.50/9.62  tff(c_36911, plain, (k2_pre_topc('#skF_6', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_34359, c_36899])).
% 17.50/9.62  tff(c_40286, plain, (![A_1066, B_1067]: (k4_subset_1(u1_struct_0(A_1066), B_1067, k2_tops_1(A_1066, B_1067))=k2_pre_topc(A_1066, B_1067) | ~m1_subset_1(B_1067, k1_zfmisc_1(u1_struct_0(A_1066))) | ~l1_pre_topc(A_1066))), inference(cnfTransformation, [status(thm)], [f_149])).
% 17.50/9.62  tff(c_40314, plain, (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k2_pre_topc('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_100, c_40286])).
% 17.50/9.62  tff(c_40331, plain, (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_36911, c_40314])).
% 17.50/9.62  tff(c_35390, plain, (k4_xboole_0(u1_struct_0('#skF_6'), '#skF_7')=k3_subset_1(u1_struct_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_100, c_35374])).
% 17.50/9.62  tff(c_35466, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_35390, c_113])).
% 17.50/9.62  tff(c_37643, plain, (![A_984, B_985]: (k2_tops_1(A_984, k3_subset_1(u1_struct_0(A_984), B_985))=k2_tops_1(A_984, B_985) | ~m1_subset_1(B_985, k1_zfmisc_1(u1_struct_0(A_984))) | ~l1_pre_topc(A_984))), inference(cnfTransformation, [status(thm)], [f_142])).
% 17.50/9.62  tff(c_37664, plain, (k2_tops_1('#skF_6', k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'))=k2_tops_1('#skF_6', '#skF_7') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_100, c_37643])).
% 17.50/9.62  tff(c_37678, plain, (k2_tops_1('#skF_6', k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'))=k2_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_37664])).
% 17.50/9.62  tff(c_37682, plain, (m1_subset_1(k2_tops_1('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_6'), '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_37678, c_92])).
% 17.50/9.62  tff(c_37686, plain, (m1_subset_1(k2_tops_1('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_35466, c_37682])).
% 17.50/9.62  tff(c_37724, plain, (r1_tarski(k2_tops_1('#skF_6', '#skF_7'), u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_37686, c_82])).
% 17.50/9.62  tff(c_37133, plain, (![A_963, B_964, C_965]: (k4_subset_1(A_963, B_964, C_965)=k2_xboole_0(B_964, C_965) | ~m1_subset_1(C_965, k1_zfmisc_1(A_963)) | ~m1_subset_1(B_964, k1_zfmisc_1(A_963)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 17.50/9.62  tff(c_51203, plain, (![B_1271, B_1272, A_1273]: (k4_subset_1(B_1271, B_1272, A_1273)=k2_xboole_0(B_1272, A_1273) | ~m1_subset_1(B_1272, k1_zfmisc_1(B_1271)) | ~r1_tarski(A_1273, B_1271))), inference(resolution, [status(thm)], [c_84, c_37133])).
% 17.50/9.62  tff(c_51411, plain, (![A_1277]: (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', A_1277)=k2_xboole_0('#skF_7', A_1277) | ~r1_tarski(A_1277, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_100, c_51203])).
% 17.50/9.62  tff(c_51458, plain, (k4_subset_1(u1_struct_0('#skF_6'), '#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k2_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_37724, c_51411])).
% 17.50/9.62  tff(c_51517, plain, (k2_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40331, c_51458])).
% 17.50/9.62  tff(c_35029, plain, (![A_869, B_870, C_871]: (r1_tarski(A_869, k2_xboole_0(B_870, C_871)) | ~r1_tarski(k4_xboole_0(A_869, B_870), C_871))), inference(cnfTransformation, [status(thm)], [f_69])).
% 17.50/9.62  tff(c_35046, plain, (![A_22, B_23]: (r1_tarski(A_22, k2_xboole_0(B_23, A_22)))), inference(resolution, [status(thm)], [c_50, c_35029])).
% 17.50/9.62  tff(c_51686, plain, (r1_tarski(k2_tops_1('#skF_6', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_51517, c_35046])).
% 17.50/9.62  tff(c_36319, plain, (![B_935, A_936]: (k4_xboole_0(B_935, A_936)=k3_subset_1(B_935, A_936) | ~r1_tarski(A_936, B_935))), inference(resolution, [status(thm)], [c_84, c_35374])).
% 17.50/9.62  tff(c_36372, plain, (![B_23, A_22]: (k4_xboole_0(k2_xboole_0(B_23, A_22), A_22)=k3_subset_1(k2_xboole_0(B_23, A_22), A_22))), inference(resolution, [status(thm)], [c_35046, c_36319])).
% 17.50/9.62  tff(c_51659, plain, (k3_subset_1(k2_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7')), k2_tops_1('#skF_6', '#skF_7'))=k4_xboole_0('#skF_7', k2_tops_1('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_51517, c_36372])).
% 17.50/9.62  tff(c_51728, plain, (k3_subset_1('#skF_7', k2_tops_1('#skF_6', '#skF_7'))=k1_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51517, c_40086, c_51659])).
% 17.50/9.62  tff(c_35161, plain, (![A_880, B_881]: (k3_subset_1(A_880, k3_subset_1(A_880, B_881))=B_881 | ~m1_subset_1(B_881, k1_zfmisc_1(A_880)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 17.50/9.62  tff(c_35170, plain, (![B_58, A_57]: (k3_subset_1(B_58, k3_subset_1(B_58, A_57))=A_57 | ~r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_84, c_35161])).
% 17.50/9.62  tff(c_59932, plain, (k3_subset_1('#skF_7', k1_tops_1('#skF_6', '#skF_7'))=k2_tops_1('#skF_6', '#skF_7') | ~r1_tarski(k2_tops_1('#skF_6', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_51728, c_35170])).
% 17.50/9.62  tff(c_59943, plain, (k3_subset_1('#skF_7', k1_tops_1('#skF_6', '#skF_7'))=k2_tops_1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_51686, c_59932])).
% 17.50/9.62  tff(c_59945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40515, c_59943])).
% 17.50/9.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.50/9.62  
% 17.50/9.62  Inference rules
% 17.50/9.62  ----------------------
% 17.50/9.62  #Ref     : 0
% 17.50/9.62  #Sup     : 14581
% 17.50/9.62  #Fact    : 0
% 17.50/9.62  #Define  : 0
% 17.50/9.62  #Split   : 8
% 17.50/9.62  #Chain   : 0
% 17.50/9.62  #Close   : 0
% 17.50/9.62  
% 17.50/9.62  Ordering : KBO
% 17.50/9.62  
% 17.50/9.62  Simplification rules
% 17.50/9.62  ----------------------
% 17.50/9.62  #Subsume      : 1102
% 17.50/9.62  #Demod        : 13022
% 17.50/9.62  #Tautology    : 7541
% 17.50/9.62  #SimpNegUnit  : 17
% 17.50/9.62  #BackRed      : 49
% 17.50/9.62  
% 17.50/9.62  #Partial instantiations: 0
% 17.50/9.62  #Strategies tried      : 1
% 17.50/9.62  
% 17.50/9.62  Timing (in seconds)
% 17.50/9.62  ----------------------
% 17.50/9.62  Preprocessing        : 0.39
% 17.50/9.62  Parsing              : 0.21
% 17.50/9.62  CNF conversion       : 0.03
% 17.50/9.62  Main loop            : 8.39
% 17.50/9.62  Inferencing          : 1.46
% 17.50/9.62  Reduction            : 4.39
% 17.50/9.62  Demodulation         : 3.70
% 17.50/9.62  BG Simplification    : 0.16
% 17.50/9.62  Subsumption          : 1.89
% 17.50/9.62  Abstraction          : 0.26
% 17.50/9.62  MUC search           : 0.00
% 17.50/9.62  Cooper               : 0.00
% 17.50/9.62  Total                : 8.84
% 17.50/9.62  Index Insertion      : 0.00
% 17.50/9.62  Index Deletion       : 0.00
% 17.50/9.62  Index Matching       : 0.00
% 17.50/9.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
