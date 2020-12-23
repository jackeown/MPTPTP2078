%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:40 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :   80 (  97 expanded)
%              Number of leaves         :   40 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   98 ( 144 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_72,plain,(
    ! [A_42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_109,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,B_67)
      | ~ m1_subset_1(A_66,k1_zfmisc_1(B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_113,plain,(
    ! [A_42] : r1_tarski(k1_xboole_0,A_42) ),
    inference(resolution,[status(thm)],[c_72,c_109])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_90,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_94,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_162,plain,(
    ! [A_89,B_90] :
      ( k6_domain_1(A_89,B_90) = k1_tarski(B_90)
      | ~ m1_subset_1(B_90,A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_171,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_162])).

tff(c_176,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_171])).

tff(c_92,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_177,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_92])).

tff(c_200,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1(k6_domain_1(A_93,B_94),k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_94,A_93)
      | v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_217,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_200])).

tff(c_225,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_217])).

tff(c_226,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_225])).

tff(c_1589,plain,(
    ! [B_555,A_556] :
      ( ~ v1_subset_1(B_555,A_556)
      | v1_xboole_0(B_555)
      | ~ m1_subset_1(B_555,k1_zfmisc_1(A_556))
      | ~ v1_zfmisc_1(A_556)
      | v1_xboole_0(A_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1598,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_1589])).

tff(c_1612,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_177,c_1598])).

tff(c_1613,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1612])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1621,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1613,c_2])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k4_enumset1(A_12,A_12,B_13,C_14,D_15,E_16) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] : k5_enumset1(A_17,A_17,B_18,C_19,D_20,E_21,F_22) = k4_enumset1(A_17,B_18,C_19,D_20,E_21,F_22) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1742,plain,(
    ! [G_644,A_648,E_645,D_647,C_642,B_646,F_643] : k6_enumset1(A_648,A_648,B_646,C_642,D_647,E_645,F_643,G_644) = k5_enumset1(A_648,B_646,C_642,D_647,E_645,F_643,G_644) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [J_41,D_33,A_30,C_32,H_37,E_34,G_36,F_35] : r2_hidden(J_41,k6_enumset1(A_30,J_41,C_32,D_33,E_34,F_35,G_36,H_37)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1837,plain,(
    ! [D_655,F_652,B_651,G_653,C_649,E_650,A_654] : r2_hidden(A_654,k5_enumset1(A_654,B_651,C_649,D_655,E_650,F_652,G_653)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1742,c_32])).

tff(c_1851,plain,(
    ! [A_657,C_656,D_660,F_659,E_661,B_658] : r2_hidden(A_657,k4_enumset1(A_657,B_658,C_656,D_660,E_661,F_659)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1837])).

tff(c_1865,plain,(
    ! [C_666,A_663,B_662,D_665,E_664] : r2_hidden(A_663,k3_enumset1(A_663,B_662,C_666,D_665,E_664)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1851])).

tff(c_1883,plain,(
    ! [A_669,B_670,C_671,D_672] : r2_hidden(A_669,k2_enumset1(A_669,B_670,C_671,D_672)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1865])).

tff(c_1897,plain,(
    ! [A_673,B_674,C_675] : r2_hidden(A_673,k1_enumset1(A_673,B_674,C_675)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1883])).

tff(c_1911,plain,(
    ! [A_676,B_677] : r2_hidden(A_676,k2_tarski(A_676,B_677)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1897])).

tff(c_1925,plain,(
    ! [A_678] : r2_hidden(A_678,k1_tarski(A_678)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1911])).

tff(c_1942,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_1925])).

tff(c_82,plain,(
    ! [B_52,A_51] :
      ( ~ r1_tarski(B_52,A_51)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1957,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1942,c_82])).

tff(c_1968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:56:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.31/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.31/1.77  
% 4.31/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.31/1.77  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.31/1.77  
% 4.31/1.77  %Foreground sorts:
% 4.31/1.77  
% 4.31/1.77  
% 4.31/1.77  %Background operators:
% 4.31/1.77  
% 4.31/1.77  
% 4.31/1.77  %Foreground operators:
% 4.31/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.31/1.77  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.31/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.31/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.31/1.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.31/1.77  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.31/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.31/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.31/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.31/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.31/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.31/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.77  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.31/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.31/1.77  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.31/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.31/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.77  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.31/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.31/1.77  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.31/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.31/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.31/1.77  
% 4.42/1.79  tff(f_75, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.42/1.79  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.42/1.79  tff(f_138, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 4.42/1.79  tff(f_112, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.42/1.79  tff(f_105, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 4.42/1.79  tff(f_126, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 4.42/1.79  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.42/1.79  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.42/1.79  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.42/1.79  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.42/1.79  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.42/1.79  tff(f_39, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 4.42/1.79  tff(f_41, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 4.42/1.79  tff(f_43, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 4.42/1.79  tff(f_73, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 4.42/1.79  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.42/1.79  tff(c_72, plain, (![A_42]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.42/1.79  tff(c_109, plain, (![A_66, B_67]: (r1_tarski(A_66, B_67) | ~m1_subset_1(A_66, k1_zfmisc_1(B_67)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.42/1.79  tff(c_113, plain, (![A_42]: (r1_tarski(k1_xboole_0, A_42))), inference(resolution, [status(thm)], [c_72, c_109])).
% 4.42/1.79  tff(c_96, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.42/1.79  tff(c_90, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.42/1.79  tff(c_94, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.42/1.79  tff(c_162, plain, (![A_89, B_90]: (k6_domain_1(A_89, B_90)=k1_tarski(B_90) | ~m1_subset_1(B_90, A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.42/1.79  tff(c_171, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_94, c_162])).
% 4.42/1.79  tff(c_176, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_96, c_171])).
% 4.42/1.79  tff(c_92, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.42/1.79  tff(c_177, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_92])).
% 4.42/1.79  tff(c_200, plain, (![A_93, B_94]: (m1_subset_1(k6_domain_1(A_93, B_94), k1_zfmisc_1(A_93)) | ~m1_subset_1(B_94, A_93) | v1_xboole_0(A_93))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.42/1.79  tff(c_217, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_176, c_200])).
% 4.42/1.79  tff(c_225, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_217])).
% 4.42/1.79  tff(c_226, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_96, c_225])).
% 4.42/1.79  tff(c_1589, plain, (![B_555, A_556]: (~v1_subset_1(B_555, A_556) | v1_xboole_0(B_555) | ~m1_subset_1(B_555, k1_zfmisc_1(A_556)) | ~v1_zfmisc_1(A_556) | v1_xboole_0(A_556))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.42/1.79  tff(c_1598, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_226, c_1589])).
% 4.42/1.79  tff(c_1612, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_177, c_1598])).
% 4.42/1.79  tff(c_1613, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_96, c_1612])).
% 4.42/1.79  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.42/1.79  tff(c_1621, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1613, c_2])).
% 4.42/1.79  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.42/1.79  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.42/1.79  tff(c_8, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.42/1.79  tff(c_10, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.42/1.79  tff(c_12, plain, (![E_16, D_15, C_14, A_12, B_13]: (k4_enumset1(A_12, A_12, B_13, C_14, D_15, E_16)=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.79  tff(c_14, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (k5_enumset1(A_17, A_17, B_18, C_19, D_20, E_21, F_22)=k4_enumset1(A_17, B_18, C_19, D_20, E_21, F_22))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.42/1.79  tff(c_1742, plain, (![G_644, A_648, E_645, D_647, C_642, B_646, F_643]: (k6_enumset1(A_648, A_648, B_646, C_642, D_647, E_645, F_643, G_644)=k5_enumset1(A_648, B_646, C_642, D_647, E_645, F_643, G_644))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.79  tff(c_32, plain, (![J_41, D_33, A_30, C_32, H_37, E_34, G_36, F_35]: (r2_hidden(J_41, k6_enumset1(A_30, J_41, C_32, D_33, E_34, F_35, G_36, H_37)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.42/1.79  tff(c_1837, plain, (![D_655, F_652, B_651, G_653, C_649, E_650, A_654]: (r2_hidden(A_654, k5_enumset1(A_654, B_651, C_649, D_655, E_650, F_652, G_653)))), inference(superposition, [status(thm), theory('equality')], [c_1742, c_32])).
% 4.42/1.79  tff(c_1851, plain, (![A_657, C_656, D_660, F_659, E_661, B_658]: (r2_hidden(A_657, k4_enumset1(A_657, B_658, C_656, D_660, E_661, F_659)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1837])).
% 4.42/1.79  tff(c_1865, plain, (![C_666, A_663, B_662, D_665, E_664]: (r2_hidden(A_663, k3_enumset1(A_663, B_662, C_666, D_665, E_664)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1851])).
% 4.42/1.79  tff(c_1883, plain, (![A_669, B_670, C_671, D_672]: (r2_hidden(A_669, k2_enumset1(A_669, B_670, C_671, D_672)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1865])).
% 4.42/1.79  tff(c_1897, plain, (![A_673, B_674, C_675]: (r2_hidden(A_673, k1_enumset1(A_673, B_674, C_675)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1883])).
% 4.42/1.79  tff(c_1911, plain, (![A_676, B_677]: (r2_hidden(A_676, k2_tarski(A_676, B_677)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1897])).
% 4.42/1.79  tff(c_1925, plain, (![A_678]: (r2_hidden(A_678, k1_tarski(A_678)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1911])).
% 4.42/1.79  tff(c_1942, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1621, c_1925])).
% 4.42/1.79  tff(c_82, plain, (![B_52, A_51]: (~r1_tarski(B_52, A_51) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/1.79  tff(c_1957, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_1942, c_82])).
% 4.42/1.79  tff(c_1968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_1957])).
% 4.42/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.79  
% 4.42/1.79  Inference rules
% 4.42/1.79  ----------------------
% 4.42/1.79  #Ref     : 0
% 4.42/1.79  #Sup     : 425
% 4.42/1.79  #Fact    : 0
% 4.42/1.79  #Define  : 0
% 4.42/1.79  #Split   : 3
% 4.42/1.79  #Chain   : 0
% 4.42/1.79  #Close   : 0
% 4.42/1.79  
% 4.42/1.79  Ordering : KBO
% 4.42/1.79  
% 4.42/1.79  Simplification rules
% 4.42/1.79  ----------------------
% 4.42/1.79  #Subsume      : 29
% 4.42/1.79  #Demod        : 159
% 4.42/1.79  #Tautology    : 145
% 4.42/1.79  #SimpNegUnit  : 34
% 4.42/1.79  #BackRed      : 22
% 4.42/1.79  
% 4.42/1.79  #Partial instantiations: 0
% 4.42/1.79  #Strategies tried      : 1
% 4.42/1.79  
% 4.42/1.79  Timing (in seconds)
% 4.42/1.79  ----------------------
% 4.42/1.79  Preprocessing        : 0.38
% 4.42/1.79  Parsing              : 0.18
% 4.42/1.79  CNF conversion       : 0.03
% 4.42/1.79  Main loop            : 0.59
% 4.42/1.79  Inferencing          : 0.20
% 4.42/1.79  Reduction            : 0.18
% 4.42/1.79  Demodulation         : 0.11
% 4.42/1.79  BG Simplification    : 0.03
% 4.42/1.79  Subsumption          : 0.14
% 4.42/1.79  Abstraction          : 0.04
% 4.42/1.79  MUC search           : 0.00
% 4.42/1.79  Cooper               : 0.00
% 4.42/1.79  Total                : 1.00
% 4.42/1.79  Index Insertion      : 0.00
% 4.42/1.79  Index Deletion       : 0.00
% 4.42/1.79  Index Matching       : 0.00
% 4.42/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
