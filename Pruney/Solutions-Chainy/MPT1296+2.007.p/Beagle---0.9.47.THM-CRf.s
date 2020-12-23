%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:41 EST 2020

% Result     : Theorem 8.56s
% Output     : CNFRefutation 8.68s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 511 expanded)
%              Number of leaves         :   32 ( 177 expanded)
%              Depth                    :   14
%              Number of atoms          :  251 (1111 expanded)
%              Number of equality atoms :   78 ( 353 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_102,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k7_setfam_1(A_12,B_13),k1_zfmisc_1(k1_zfmisc_1(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8650,plain,(
    ! [A_339,B_340] :
      ( k7_setfam_1(A_339,k7_setfam_1(A_339,B_340)) = B_340
      | ~ m1_subset_1(B_340,k1_zfmisc_1(k1_zfmisc_1(A_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8657,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_8650])).

tff(c_9141,plain,(
    ! [A_370,C_371,B_372] :
      ( r2_hidden(k3_subset_1(A_370,C_371),k7_setfam_1(A_370,B_372))
      | ~ r2_hidden(C_371,B_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(A_370))
      | ~ m1_subset_1(B_372,k1_zfmisc_1(k1_zfmisc_1(A_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9168,plain,(
    ! [C_371] :
      ( r2_hidden(k3_subset_1('#skF_3',C_371),'#skF_4')
      | ~ r2_hidden(C_371,k7_setfam_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_371,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8657,c_9141])).

tff(c_9259,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9168])).

tff(c_9265,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16,c_9259])).

tff(c_9272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_9265])).

tff(c_9274,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_9168])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k5_setfam_1(A_16,B_17) = k3_tarski(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_9296,plain,(
    k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = k3_tarski(k7_setfam_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9274,c_20])).

tff(c_42,plain,(
    k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) != k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9431,plain,(
    k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) != k3_tarski(k7_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9296,c_42])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k5_setfam_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(k1_zfmisc_1(A_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_9435,plain,
    ( m1_subset_1(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9296,c_14])).

tff(c_9439,plain,(
    m1_subset_1(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9274,c_9435])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9485,plain,(
    r1_tarski(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_9439,c_22])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_2'(A_29),A_29)
      | k3_tarski(A_29) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_183,plain,(
    ! [A_62,C_63,B_64] :
      ( m1_subset_1(A_62,C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_190,plain,(
    ! [A_65] :
      ( m1_subset_1(A_65,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_183])).

tff(c_201,plain,(
    ! [A_66] :
      ( r1_tarski(A_66,'#skF_3')
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_190,c_22])).

tff(c_211,plain,
    ( r1_tarski('#skF_2'('#skF_4'),'#skF_3')
    | k3_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_226,plain,(
    k3_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_103,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [A_29,B_32] :
      ( k3_tarski(A_29) != k1_xboole_0
      | ~ r2_hidden(B_32,A_29)
      | k1_xboole_0 = B_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_340,plain,(
    ! [A_83,B_84] :
      ( k3_tarski(A_83) != k1_xboole_0
      | '#skF_1'(A_83,B_84) = k1_xboole_0
      | r1_tarski(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_103,c_34])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_361,plain,(
    ! [A_85] :
      ( k1_xboole_0 = A_85
      | k3_tarski(A_85) != k1_xboole_0
      | '#skF_1'(A_85,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_340,c_10])).

tff(c_364,plain,
    ( k1_xboole_0 = '#skF_4'
    | '#skF_1'('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_361])).

tff(c_373,plain,(
    '#skF_1'('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_364])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_389,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_6])).

tff(c_437,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_440,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_437,c_10])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_440])).

tff(c_445,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44),A_44)
      | k3_tarski(A_44) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    ! [B_28,A_27] :
      ( ~ r1_tarski(B_28,A_27)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_80,plain,(
    ! [A_45] :
      ( ~ r1_tarski(A_45,'#skF_2'(A_45))
      | k3_tarski(A_45) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_75,c_32])).

tff(c_85,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_212,plain,(
    ! [A_67,B_68] :
      ( k5_setfam_1(A_67,B_68) = k3_tarski(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_252,plain,(
    ! [A_73,A_74] :
      ( k5_setfam_1(A_73,A_74) = k3_tarski(A_74)
      | ~ r1_tarski(A_74,k1_zfmisc_1(A_73)) ) ),
    inference(resolution,[status(thm)],[c_24,c_212])).

tff(c_263,plain,(
    ! [A_73] : k5_setfam_1(A_73,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_252])).

tff(c_268,plain,(
    ! [A_73] : k5_setfam_1(A_73,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_263])).

tff(c_395,plain,(
    ! [A_86,B_87] :
      ( m1_subset_1(k5_setfam_1(A_86,B_87),k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(A_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_647,plain,(
    ! [A_98] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_98))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_395])).

tff(c_653,plain,(
    ! [A_98] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_98))
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_98)) ) ),
    inference(resolution,[status(thm)],[c_24,c_647])).

tff(c_657,plain,(
    ! [A_98] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_98)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_653])).

tff(c_285,plain,(
    ! [A_77,B_78] :
      ( k7_setfam_1(A_77,k7_setfam_1(A_77,B_78)) = B_78
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_292,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_285])).

tff(c_845,plain,(
    ! [A_110,C_111,B_112] :
      ( r2_hidden(k3_subset_1(A_110,C_111),k7_setfam_1(A_110,B_112))
      | ~ r2_hidden(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_869,plain,(
    ! [C_111] :
      ( r2_hidden(k3_subset_1('#skF_3',C_111),'#skF_4')
      | ~ r2_hidden(C_111,k7_setfam_1('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_111,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_845])).

tff(c_905,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_869])).

tff(c_908,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_16,c_905])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_908])).

tff(c_917,plain,(
    m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_869])).

tff(c_936,plain,(
    k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = k3_tarski(k7_setfam_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_917,c_20])).

tff(c_976,plain,(
    k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) != k3_tarski(k7_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_42])).

tff(c_980,plain,
    ( m1_subset_1(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_14])).

tff(c_984,plain,(
    m1_subset_1(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_980])).

tff(c_1023,plain,(
    r1_tarski(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_984,c_22])).

tff(c_683,plain,(
    ! [A_100,B_101] :
      ( k6_setfam_1(A_100,k7_setfam_1(A_100,B_101)) = k3_subset_1(A_100,k5_setfam_1(A_100,B_101))
      | k1_xboole_0 = B_101
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k1_zfmisc_1(A_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6865,plain,(
    ! [A_285,B_286] :
      ( k6_setfam_1(A_285,k7_setfam_1(A_285,k7_setfam_1(A_285,B_286))) = k3_subset_1(A_285,k5_setfam_1(A_285,k7_setfam_1(A_285,B_286)))
      | k7_setfam_1(A_285,B_286) = k1_xboole_0
      | ~ m1_subset_1(B_286,k1_zfmisc_1(k1_zfmisc_1(A_285))) ) ),
    inference(resolution,[status(thm)],[c_16,c_683])).

tff(c_6891,plain,
    ( k6_setfam_1('#skF_3',k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')))
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_6865])).

tff(c_6906,plain,
    ( k3_subset_1('#skF_3',k3_tarski(k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4')
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_292,c_6891])).

tff(c_7228,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_6906])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_subset_1(A_8,k3_subset_1(A_8,B_9)) = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_199,plain,(
    ! [A_65] :
      ( k3_subset_1('#skF_3',k3_subset_1('#skF_3',A_65)) = A_65
      | ~ r2_hidden(A_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_190,c_12])).

tff(c_986,plain,(
    ! [C_116,B_117,A_118] :
      ( r2_hidden(C_116,B_117)
      | ~ r2_hidden(k3_subset_1(A_118,C_116),k7_setfam_1(A_118,B_117))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_118))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(k1_zfmisc_1(A_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1001,plain,(
    ! [C_116] :
      ( r2_hidden(C_116,k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(k3_subset_1('#skF_3',C_116),'#skF_4')
      | ~ m1_subset_1(C_116,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(k7_setfam_1('#skF_3','#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_986])).

tff(c_2054,plain,(
    ! [C_157] :
      ( r2_hidden(C_157,k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(k3_subset_1('#skF_3',C_157),'#skF_4')
      | ~ m1_subset_1(C_157,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_1001])).

tff(c_3175,plain,(
    ! [A_189] :
      ( r2_hidden(k3_subset_1('#skF_3',A_189),k7_setfam_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_189,'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_3',A_189),k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_189,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_2054])).

tff(c_30,plain,(
    ! [A_24,C_26,B_25] :
      ( m1_subset_1(A_24,C_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_26))
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_198,plain,(
    ! [A_24,A_65] :
      ( m1_subset_1(A_24,'#skF_3')
      | ~ r2_hidden(A_24,A_65)
      | ~ r2_hidden(A_65,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_190,c_30])).

tff(c_3222,plain,(
    ! [A_189] :
      ( m1_subset_1(k3_subset_1('#skF_3',A_189),'#skF_3')
      | ~ r2_hidden(k7_setfam_1('#skF_3','#skF_4'),'#skF_4')
      | ~ m1_subset_1(k3_subset_1('#skF_3',A_189),k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_189,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3175,c_198])).

tff(c_3701,plain,(
    ~ r2_hidden(k7_setfam_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3222])).

tff(c_7234,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7228,c_3701])).

tff(c_7255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_7234])).

tff(c_7256,plain,(
    k3_subset_1('#skF_3',k3_tarski(k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6906])).

tff(c_139,plain,(
    ! [A_58,B_59] :
      ( k3_subset_1(A_58,k3_subset_1(A_58,B_59)) = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_144,plain,(
    ! [B_19,A_18] :
      ( k3_subset_1(B_19,k3_subset_1(B_19,A_18)) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_24,c_139])).

tff(c_7292,plain,
    ( k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) = k3_tarski(k7_setfam_1('#skF_3','#skF_4'))
    | ~ r1_tarski(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7256,c_144])).

tff(c_7316,plain,(
    k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) = k3_tarski(k7_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1023,c_7292])).

tff(c_7318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_976,c_7316])).

tff(c_7320,plain,(
    r2_hidden(k7_setfam_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3222])).

tff(c_7339,plain,
    ( k3_tarski('#skF_4') != k1_xboole_0
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7320,c_34])).

tff(c_7352,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_7339])).

tff(c_8451,plain,(
    ! [A_327,B_328,C_329] :
      ( ~ r1_tarski(k7_setfam_1(A_327,B_328),k3_subset_1(A_327,C_329))
      | ~ r2_hidden(C_329,B_328)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(A_327))
      | ~ m1_subset_1(B_328,k1_zfmisc_1(k1_zfmisc_1(A_327))) ) ),
    inference(resolution,[status(thm)],[c_845,c_32])).

tff(c_8463,plain,(
    ! [C_329] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_3',C_329))
      | ~ r2_hidden(C_329,'#skF_4')
      | ~ m1_subset_1(C_329,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7352,c_8451])).

tff(c_8555,plain,(
    ! [C_331] :
      ( ~ r2_hidden(C_331,'#skF_4')
      | ~ m1_subset_1(C_331,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_8463])).

tff(c_8563,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_657,c_8555])).

tff(c_8583,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_8563])).

tff(c_8585,plain,(
    k3_tarski('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_189,plain,(
    ! [A_62] :
      ( m1_subset_1(A_62,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_62,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_183])).

tff(c_9016,plain,(
    ! [A_366,B_367] :
      ( k6_setfam_1(A_366,k7_setfam_1(A_366,B_367)) = k3_subset_1(A_366,k5_setfam_1(A_366,B_367))
      | k1_xboole_0 = B_367
      | ~ m1_subset_1(B_367,k1_zfmisc_1(k1_zfmisc_1(A_366))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_14655,plain,(
    ! [A_540,B_541] :
      ( k6_setfam_1(A_540,k7_setfam_1(A_540,k7_setfam_1(A_540,B_541))) = k3_subset_1(A_540,k5_setfam_1(A_540,k7_setfam_1(A_540,B_541)))
      | k7_setfam_1(A_540,B_541) = k1_xboole_0
      | ~ m1_subset_1(B_541,k1_zfmisc_1(k1_zfmisc_1(A_540))) ) ),
    inference(resolution,[status(thm)],[c_16,c_9016])).

tff(c_14678,plain,
    ( k6_setfam_1('#skF_3',k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4'))) = k3_subset_1('#skF_3',k5_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')))
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_14655])).

tff(c_14691,plain,
    ( k3_subset_1('#skF_3',k3_tarski(k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4')
    | k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_9296,c_8657,c_14678])).

tff(c_14904,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14691])).

tff(c_9182,plain,(
    ! [A_370,B_372,C_371] :
      ( ~ r1_tarski(k7_setfam_1(A_370,B_372),k3_subset_1(A_370,C_371))
      | ~ r2_hidden(C_371,B_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(A_370))
      | ~ m1_subset_1(B_372,k1_zfmisc_1(k1_zfmisc_1(A_370))) ) ),
    inference(resolution,[status(thm)],[c_9141,c_32])).

tff(c_14938,plain,(
    ! [C_371] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_3',C_371))
      | ~ r2_hidden(C_371,'#skF_4')
      | ~ m1_subset_1(C_371,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14904,c_9182])).

tff(c_15123,plain,(
    ! [C_547] :
      ( ~ r2_hidden(C_547,'#skF_4')
      | ~ m1_subset_1(C_547,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_14938])).

tff(c_15157,plain,(
    ! [A_548] : ~ r2_hidden(A_548,'#skF_4') ),
    inference(resolution,[status(thm)],[c_189,c_15123])).

tff(c_15177,plain,(
    k3_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_15157])).

tff(c_15185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8585,c_15177])).

tff(c_15186,plain,(
    k3_subset_1('#skF_3',k3_tarski(k7_setfam_1('#skF_3','#skF_4'))) = k6_setfam_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_14691])).

tff(c_15311,plain,
    ( k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) = k3_tarski(k7_setfam_1('#skF_3','#skF_4'))
    | ~ r1_tarski(k3_tarski(k7_setfam_1('#skF_3','#skF_4')),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_15186,c_144])).

tff(c_15331,plain,(
    k3_subset_1('#skF_3',k6_setfam_1('#skF_3','#skF_4')) = k3_tarski(k7_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9485,c_15311])).

tff(c_15333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9431,c_15331])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.56/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.56/3.18  
% 8.56/3.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.56/3.18  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.56/3.18  
% 8.56/3.18  %Foreground sorts:
% 8.56/3.18  
% 8.56/3.18  
% 8.56/3.18  %Background operators:
% 8.56/3.18  
% 8.56/3.18  
% 8.56/3.18  %Foreground operators:
% 8.56/3.18  tff('#skF_2', type, '#skF_2': $i > $i).
% 8.56/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.56/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.56/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.56/3.18  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 8.56/3.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.56/3.18  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.56/3.18  tff('#skF_3', type, '#skF_3': $i).
% 8.56/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.56/3.18  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 8.56/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.56/3.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.56/3.18  tff('#skF_4', type, '#skF_4': $i).
% 8.56/3.18  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 8.56/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.56/3.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.56/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.56/3.18  
% 8.68/3.21  tff(f_117, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 8.68/3.21  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 8.68/3.21  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 8.68/3.21  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 8.68/3.21  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 8.68/3.21  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 8.68/3.21  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.68/3.21  tff(f_102, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 8.68/3.21  tff(f_77, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.68/3.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.68/3.21  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.68/3.21  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.68/3.21  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.68/3.21  tff(f_109, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 8.68/3.21  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 8.68/3.21  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.68/3.21  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k7_setfam_1(A_12, B_13), k1_zfmisc_1(k1_zfmisc_1(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.68/3.21  tff(c_8650, plain, (![A_339, B_340]: (k7_setfam_1(A_339, k7_setfam_1(A_339, B_340))=B_340 | ~m1_subset_1(B_340, k1_zfmisc_1(k1_zfmisc_1(A_339))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.68/3.21  tff(c_8657, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_8650])).
% 8.68/3.21  tff(c_9141, plain, (![A_370, C_371, B_372]: (r2_hidden(k3_subset_1(A_370, C_371), k7_setfam_1(A_370, B_372)) | ~r2_hidden(C_371, B_372) | ~m1_subset_1(C_371, k1_zfmisc_1(A_370)) | ~m1_subset_1(B_372, k1_zfmisc_1(k1_zfmisc_1(A_370))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.68/3.21  tff(c_9168, plain, (![C_371]: (r2_hidden(k3_subset_1('#skF_3', C_371), '#skF_4') | ~r2_hidden(C_371, k7_setfam_1('#skF_3', '#skF_4')) | ~m1_subset_1(C_371, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_8657, c_9141])).
% 8.68/3.21  tff(c_9259, plain, (~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_9168])).
% 8.68/3.21  tff(c_9265, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_9259])).
% 8.68/3.21  tff(c_9272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_9265])).
% 8.68/3.21  tff(c_9274, plain, (m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_9168])).
% 8.68/3.21  tff(c_20, plain, (![A_16, B_17]: (k5_setfam_1(A_16, B_17)=k3_tarski(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.68/3.21  tff(c_9296, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))=k3_tarski(k7_setfam_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9274, c_20])).
% 8.68/3.21  tff(c_42, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))!=k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.68/3.21  tff(c_9431, plain, (k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))!=k3_tarski(k7_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9296, c_42])).
% 8.68/3.21  tff(c_14, plain, (![A_10, B_11]: (m1_subset_1(k5_setfam_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(k1_zfmisc_1(A_10))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.68/3.21  tff(c_9435, plain, (m1_subset_1(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9296, c_14])).
% 8.68/3.21  tff(c_9439, plain, (m1_subset_1(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9274, c_9435])).
% 8.68/3.21  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.68/3.21  tff(c_9485, plain, (r1_tarski(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_9439, c_22])).
% 8.68/3.21  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.68/3.21  tff(c_36, plain, (![A_29]: (r2_hidden('#skF_2'(A_29), A_29) | k3_tarski(A_29)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.68/3.21  tff(c_183, plain, (![A_62, C_63, B_64]: (m1_subset_1(A_62, C_63) | ~m1_subset_1(B_64, k1_zfmisc_1(C_63)) | ~r2_hidden(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.68/3.21  tff(c_190, plain, (![A_65]: (m1_subset_1(A_65, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_65, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_183])).
% 8.68/3.21  tff(c_201, plain, (![A_66]: (r1_tarski(A_66, '#skF_3') | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_190, c_22])).
% 8.68/3.21  tff(c_211, plain, (r1_tarski('#skF_2'('#skF_4'), '#skF_3') | k3_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_201])).
% 8.68/3.21  tff(c_226, plain, (k3_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_211])).
% 8.68/3.21  tff(c_103, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.68/3.21  tff(c_34, plain, (![A_29, B_32]: (k3_tarski(A_29)!=k1_xboole_0 | ~r2_hidden(B_32, A_29) | k1_xboole_0=B_32)), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.68/3.21  tff(c_340, plain, (![A_83, B_84]: (k3_tarski(A_83)!=k1_xboole_0 | '#skF_1'(A_83, B_84)=k1_xboole_0 | r1_tarski(A_83, B_84))), inference(resolution, [status(thm)], [c_103, c_34])).
% 8.68/3.21  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.68/3.21  tff(c_361, plain, (![A_85]: (k1_xboole_0=A_85 | k3_tarski(A_85)!=k1_xboole_0 | '#skF_1'(A_85, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_340, c_10])).
% 8.68/3.21  tff(c_364, plain, (k1_xboole_0='#skF_4' | '#skF_1'('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_226, c_361])).
% 8.68/3.21  tff(c_373, plain, ('#skF_1'('#skF_4', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_364])).
% 8.68/3.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.68/3.21  tff(c_389, plain, (r2_hidden(k1_xboole_0, '#skF_4') | r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_373, c_6])).
% 8.68/3.21  tff(c_437, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_389])).
% 8.68/3.21  tff(c_440, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_437, c_10])).
% 8.68/3.21  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_440])).
% 8.68/3.21  tff(c_445, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_389])).
% 8.68/3.21  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.68/3.21  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.68/3.21  tff(c_75, plain, (![A_44]: (r2_hidden('#skF_2'(A_44), A_44) | k3_tarski(A_44)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.68/3.21  tff(c_32, plain, (![B_28, A_27]: (~r1_tarski(B_28, A_27) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.68/3.21  tff(c_80, plain, (![A_45]: (~r1_tarski(A_45, '#skF_2'(A_45)) | k3_tarski(A_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_75, c_32])).
% 8.68/3.21  tff(c_85, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_80])).
% 8.68/3.21  tff(c_212, plain, (![A_67, B_68]: (k5_setfam_1(A_67, B_68)=k3_tarski(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.68/3.21  tff(c_252, plain, (![A_73, A_74]: (k5_setfam_1(A_73, A_74)=k3_tarski(A_74) | ~r1_tarski(A_74, k1_zfmisc_1(A_73)))), inference(resolution, [status(thm)], [c_24, c_212])).
% 8.68/3.21  tff(c_263, plain, (![A_73]: (k5_setfam_1(A_73, k1_xboole_0)=k3_tarski(k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_252])).
% 8.68/3.21  tff(c_268, plain, (![A_73]: (k5_setfam_1(A_73, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_263])).
% 8.68/3.21  tff(c_395, plain, (![A_86, B_87]: (m1_subset_1(k5_setfam_1(A_86, B_87), k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(A_86))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.68/3.21  tff(c_647, plain, (![A_98]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_98)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_98))))), inference(superposition, [status(thm), theory('equality')], [c_268, c_395])).
% 8.68/3.21  tff(c_653, plain, (![A_98]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_98)) | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_98)))), inference(resolution, [status(thm)], [c_24, c_647])).
% 8.68/3.21  tff(c_657, plain, (![A_98]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_98)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_653])).
% 8.68/3.21  tff(c_285, plain, (![A_77, B_78]: (k7_setfam_1(A_77, k7_setfam_1(A_77, B_78))=B_78 | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.68/3.21  tff(c_292, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_285])).
% 8.68/3.21  tff(c_845, plain, (![A_110, C_111, B_112]: (r2_hidden(k3_subset_1(A_110, C_111), k7_setfam_1(A_110, B_112)) | ~r2_hidden(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_110))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.68/3.21  tff(c_869, plain, (![C_111]: (r2_hidden(k3_subset_1('#skF_3', C_111), '#skF_4') | ~r2_hidden(C_111, k7_setfam_1('#skF_3', '#skF_4')) | ~m1_subset_1(C_111, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_292, c_845])).
% 8.68/3.21  tff(c_905, plain, (~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_869])).
% 8.68/3.21  tff(c_908, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_16, c_905])).
% 8.68/3.21  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_908])).
% 8.68/3.21  tff(c_917, plain, (m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_869])).
% 8.68/3.21  tff(c_936, plain, (k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))=k3_tarski(k7_setfam_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_917, c_20])).
% 8.68/3.21  tff(c_976, plain, (k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))!=k3_tarski(k7_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_936, c_42])).
% 8.68/3.21  tff(c_980, plain, (m1_subset_1(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_936, c_14])).
% 8.68/3.21  tff(c_984, plain, (m1_subset_1(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_980])).
% 8.68/3.21  tff(c_1023, plain, (r1_tarski(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_984, c_22])).
% 8.68/3.21  tff(c_683, plain, (![A_100, B_101]: (k6_setfam_1(A_100, k7_setfam_1(A_100, B_101))=k3_subset_1(A_100, k5_setfam_1(A_100, B_101)) | k1_xboole_0=B_101 | ~m1_subset_1(B_101, k1_zfmisc_1(k1_zfmisc_1(A_100))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.68/3.21  tff(c_6865, plain, (![A_285, B_286]: (k6_setfam_1(A_285, k7_setfam_1(A_285, k7_setfam_1(A_285, B_286)))=k3_subset_1(A_285, k5_setfam_1(A_285, k7_setfam_1(A_285, B_286))) | k7_setfam_1(A_285, B_286)=k1_xboole_0 | ~m1_subset_1(B_286, k1_zfmisc_1(k1_zfmisc_1(A_285))))), inference(resolution, [status(thm)], [c_16, c_683])).
% 8.68/3.21  tff(c_6891, plain, (k6_setfam_1('#skF_3', k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_6865])).
% 8.68/3.21  tff(c_6906, plain, (k3_subset_1('#skF_3', k3_tarski(k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4') | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_936, c_292, c_6891])).
% 8.68/3.21  tff(c_7228, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_6906])).
% 8.68/3.21  tff(c_12, plain, (![A_8, B_9]: (k3_subset_1(A_8, k3_subset_1(A_8, B_9))=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.68/3.21  tff(c_199, plain, (![A_65]: (k3_subset_1('#skF_3', k3_subset_1('#skF_3', A_65))=A_65 | ~r2_hidden(A_65, '#skF_4'))), inference(resolution, [status(thm)], [c_190, c_12])).
% 8.68/3.21  tff(c_986, plain, (![C_116, B_117, A_118]: (r2_hidden(C_116, B_117) | ~r2_hidden(k3_subset_1(A_118, C_116), k7_setfam_1(A_118, B_117)) | ~m1_subset_1(C_116, k1_zfmisc_1(A_118)) | ~m1_subset_1(B_117, k1_zfmisc_1(k1_zfmisc_1(A_118))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.68/3.21  tff(c_1001, plain, (![C_116]: (r2_hidden(C_116, k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(k3_subset_1('#skF_3', C_116), '#skF_4') | ~m1_subset_1(C_116, k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k7_setfam_1('#skF_3', '#skF_4'), k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_292, c_986])).
% 8.68/3.21  tff(c_2054, plain, (![C_157]: (r2_hidden(C_157, k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(k3_subset_1('#skF_3', C_157), '#skF_4') | ~m1_subset_1(C_157, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_917, c_1001])).
% 8.68/3.21  tff(c_3175, plain, (![A_189]: (r2_hidden(k3_subset_1('#skF_3', A_189), k7_setfam_1('#skF_3', '#skF_4')) | ~r2_hidden(A_189, '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', A_189), k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_189, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_2054])).
% 8.68/3.21  tff(c_30, plain, (![A_24, C_26, B_25]: (m1_subset_1(A_24, C_26) | ~m1_subset_1(B_25, k1_zfmisc_1(C_26)) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.68/3.21  tff(c_198, plain, (![A_24, A_65]: (m1_subset_1(A_24, '#skF_3') | ~r2_hidden(A_24, A_65) | ~r2_hidden(A_65, '#skF_4'))), inference(resolution, [status(thm)], [c_190, c_30])).
% 8.68/3.21  tff(c_3222, plain, (![A_189]: (m1_subset_1(k3_subset_1('#skF_3', A_189), '#skF_3') | ~r2_hidden(k7_setfam_1('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k3_subset_1('#skF_3', A_189), k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_189, '#skF_4'))), inference(resolution, [status(thm)], [c_3175, c_198])).
% 8.68/3.21  tff(c_3701, plain, (~r2_hidden(k7_setfam_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3222])).
% 8.68/3.21  tff(c_7234, plain, (~r2_hidden(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7228, c_3701])).
% 8.68/3.21  tff(c_7255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_7234])).
% 8.68/3.21  tff(c_7256, plain, (k3_subset_1('#skF_3', k3_tarski(k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_6906])).
% 8.68/3.21  tff(c_139, plain, (![A_58, B_59]: (k3_subset_1(A_58, k3_subset_1(A_58, B_59))=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.68/3.21  tff(c_144, plain, (![B_19, A_18]: (k3_subset_1(B_19, k3_subset_1(B_19, A_18))=A_18 | ~r1_tarski(A_18, B_19))), inference(resolution, [status(thm)], [c_24, c_139])).
% 8.68/3.21  tff(c_7292, plain, (k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))=k3_tarski(k7_setfam_1('#skF_3', '#skF_4')) | ~r1_tarski(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7256, c_144])).
% 8.68/3.21  tff(c_7316, plain, (k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))=k3_tarski(k7_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1023, c_7292])).
% 8.68/3.21  tff(c_7318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_976, c_7316])).
% 8.68/3.21  tff(c_7320, plain, (r2_hidden(k7_setfam_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_3222])).
% 8.68/3.21  tff(c_7339, plain, (k3_tarski('#skF_4')!=k1_xboole_0 | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_7320, c_34])).
% 8.68/3.21  tff(c_7352, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_226, c_7339])).
% 8.68/3.21  tff(c_8451, plain, (![A_327, B_328, C_329]: (~r1_tarski(k7_setfam_1(A_327, B_328), k3_subset_1(A_327, C_329)) | ~r2_hidden(C_329, B_328) | ~m1_subset_1(C_329, k1_zfmisc_1(A_327)) | ~m1_subset_1(B_328, k1_zfmisc_1(k1_zfmisc_1(A_327))))), inference(resolution, [status(thm)], [c_845, c_32])).
% 8.68/3.21  tff(c_8463, plain, (![C_329]: (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_3', C_329)) | ~r2_hidden(C_329, '#skF_4') | ~m1_subset_1(C_329, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_7352, c_8451])).
% 8.68/3.21  tff(c_8555, plain, (![C_331]: (~r2_hidden(C_331, '#skF_4') | ~m1_subset_1(C_331, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_8463])).
% 8.68/3.21  tff(c_8563, plain, (~r2_hidden(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_657, c_8555])).
% 8.68/3.21  tff(c_8583, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_445, c_8563])).
% 8.68/3.21  tff(c_8585, plain, (k3_tarski('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_211])).
% 8.68/3.21  tff(c_189, plain, (![A_62]: (m1_subset_1(A_62, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_62, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_183])).
% 8.68/3.21  tff(c_9016, plain, (![A_366, B_367]: (k6_setfam_1(A_366, k7_setfam_1(A_366, B_367))=k3_subset_1(A_366, k5_setfam_1(A_366, B_367)) | k1_xboole_0=B_367 | ~m1_subset_1(B_367, k1_zfmisc_1(k1_zfmisc_1(A_366))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.68/3.21  tff(c_14655, plain, (![A_540, B_541]: (k6_setfam_1(A_540, k7_setfam_1(A_540, k7_setfam_1(A_540, B_541)))=k3_subset_1(A_540, k5_setfam_1(A_540, k7_setfam_1(A_540, B_541))) | k7_setfam_1(A_540, B_541)=k1_xboole_0 | ~m1_subset_1(B_541, k1_zfmisc_1(k1_zfmisc_1(A_540))))), inference(resolution, [status(thm)], [c_16, c_9016])).
% 8.68/3.21  tff(c_14678, plain, (k6_setfam_1('#skF_3', k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4')))=k3_subset_1('#skF_3', k5_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))) | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_14655])).
% 8.68/3.21  tff(c_14691, plain, (k3_subset_1('#skF_3', k3_tarski(k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4') | k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_9296, c_8657, c_14678])).
% 8.68/3.21  tff(c_14904, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14691])).
% 8.68/3.21  tff(c_9182, plain, (![A_370, B_372, C_371]: (~r1_tarski(k7_setfam_1(A_370, B_372), k3_subset_1(A_370, C_371)) | ~r2_hidden(C_371, B_372) | ~m1_subset_1(C_371, k1_zfmisc_1(A_370)) | ~m1_subset_1(B_372, k1_zfmisc_1(k1_zfmisc_1(A_370))))), inference(resolution, [status(thm)], [c_9141, c_32])).
% 8.68/3.21  tff(c_14938, plain, (![C_371]: (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_3', C_371)) | ~r2_hidden(C_371, '#skF_4') | ~m1_subset_1(C_371, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_14904, c_9182])).
% 8.68/3.21  tff(c_15123, plain, (![C_547]: (~r2_hidden(C_547, '#skF_4') | ~m1_subset_1(C_547, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_14938])).
% 8.68/3.21  tff(c_15157, plain, (![A_548]: (~r2_hidden(A_548, '#skF_4'))), inference(resolution, [status(thm)], [c_189, c_15123])).
% 8.68/3.21  tff(c_15177, plain, (k3_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_15157])).
% 8.68/3.21  tff(c_15185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8585, c_15177])).
% 8.68/3.21  tff(c_15186, plain, (k3_subset_1('#skF_3', k3_tarski(k7_setfam_1('#skF_3', '#skF_4')))=k6_setfam_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_14691])).
% 8.68/3.21  tff(c_15311, plain, (k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))=k3_tarski(k7_setfam_1('#skF_3', '#skF_4')) | ~r1_tarski(k3_tarski(k7_setfam_1('#skF_3', '#skF_4')), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_15186, c_144])).
% 8.68/3.21  tff(c_15331, plain, (k3_subset_1('#skF_3', k6_setfam_1('#skF_3', '#skF_4'))=k3_tarski(k7_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9485, c_15311])).
% 8.68/3.21  tff(c_15333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9431, c_15331])).
% 8.68/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.68/3.21  
% 8.68/3.21  Inference rules
% 8.68/3.21  ----------------------
% 8.68/3.21  #Ref     : 0
% 8.68/3.21  #Sup     : 3481
% 8.68/3.21  #Fact    : 0
% 8.68/3.21  #Define  : 0
% 8.68/3.21  #Split   : 31
% 8.68/3.21  #Chain   : 0
% 8.68/3.21  #Close   : 0
% 8.68/3.21  
% 8.68/3.21  Ordering : KBO
% 8.68/3.21  
% 8.68/3.21  Simplification rules
% 8.68/3.21  ----------------------
% 8.68/3.21  #Subsume      : 913
% 8.68/3.21  #Demod        : 2847
% 8.68/3.21  #Tautology    : 1322
% 8.68/3.21  #SimpNegUnit  : 75
% 8.68/3.21  #BackRed      : 75
% 8.68/3.21  
% 8.68/3.21  #Partial instantiations: 0
% 8.68/3.21  #Strategies tried      : 1
% 8.68/3.21  
% 8.68/3.21  Timing (in seconds)
% 8.68/3.21  ----------------------
% 8.68/3.21  Preprocessing        : 0.33
% 8.68/3.21  Parsing              : 0.18
% 8.68/3.21  CNF conversion       : 0.02
% 8.68/3.21  Main loop            : 2.13
% 8.68/3.21  Inferencing          : 0.62
% 8.68/3.21  Reduction            : 0.76
% 8.68/3.21  Demodulation         : 0.53
% 8.68/3.21  BG Simplification    : 0.07
% 8.68/3.21  Subsumption          : 0.54
% 8.68/3.21  Abstraction          : 0.08
% 8.68/3.21  MUC search           : 0.00
% 8.68/3.21  Cooper               : 0.00
% 8.68/3.21  Total                : 2.52
% 8.68/3.21  Index Insertion      : 0.00
% 8.68/3.21  Index Deletion       : 0.00
% 8.68/3.21  Index Matching       : 0.00
% 8.68/3.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
