%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:01 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 391 expanded)
%              Number of leaves         :   32 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 801 expanded)
%              Number of equality atoms :   68 ( 190 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_60,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_95,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_123,plain,(
    ! [A_61,C_62,B_63] :
      ( m1_subset_1(A_61,C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_160,plain,(
    ! [A_68] :
      ( m1_subset_1(A_68,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_68,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_123])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_168,plain,(
    ! [A_69] :
      ( r1_tarski(A_69,'#skF_4')
      | ~ r2_hidden(A_69,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_160,c_32])).

tff(c_193,plain,
    ( r1_tarski('#skF_3'('#skF_5'),'#skF_4')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_14,c_168])).

tff(c_194,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_301,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_3'(A_81),A_81)
      | A_81 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_14])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_195,plain,(
    ! [A_70] :
      ( m1_subset_1(A_70,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_70,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_202,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,'#skF_4')
      | ~ r2_hidden(A_70,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_195,c_32])).

tff(c_317,plain,
    ( r1_tarski('#skF_3'('#skF_6'),'#skF_4')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_301,c_202])).

tff(c_321,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_22,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    ! [A_17] :
      ( k8_setfam_1(A_17,k1_xboole_0) = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_48,plain,(
    ! [A_17] : k8_setfam_1(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_208,plain,(
    ! [A_17] : k8_setfam_1(A_17,'#skF_5') = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_48])).

tff(c_327,plain,(
    ! [A_17] : k8_setfam_1(A_17,'#skF_6') = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_208])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k8_setfam_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_218,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_40])).

tff(c_387,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_218])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_387])).

tff(c_392,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_245,plain,(
    ! [A_75,B_76] :
      ( k6_setfam_1(A_75,B_76) = k1_setfam_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k1_zfmisc_1(A_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_259,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_245])).

tff(c_26,plain,(
    ! [A_17,B_18] :
      ( k8_setfam_1(A_17,B_18) = k6_setfam_1(A_17,B_18)
      | k1_xboole_0 = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_515,plain,(
    ! [A_104,B_105] :
      ( k8_setfam_1(A_104,B_105) = k6_setfam_1(A_104,B_105)
      | B_105 = '#skF_5'
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_26])).

tff(c_546,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_515])).

tff(c_558,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_546])).

tff(c_559,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_558])).

tff(c_560,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_218])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k8_setfam_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_564,plain,
    ( m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_28])).

tff(c_568,plain,(
    m1_subset_1(k1_setfam_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_564])).

tff(c_574,plain,(
    r1_tarski(k1_setfam_1('#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_568,c_32])).

tff(c_579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_560,c_574])).

tff(c_581,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_42,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_setfam_1(B_29),k1_setfam_1(A_28))
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_582,plain,(
    ! [A_106] :
      ( m1_subset_1(A_106,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_106,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_123])).

tff(c_590,plain,(
    ! [A_107] :
      ( r1_tarski(A_107,'#skF_4')
      | ~ r2_hidden(A_107,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_582,c_32])).

tff(c_615,plain,
    ( r1_tarski('#skF_3'('#skF_6'),'#skF_4')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_14,c_590])).

tff(c_616,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_615])).

tff(c_617,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_581])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_625,plain,(
    ! [A_13] : k4_xboole_0('#skF_6',A_13) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_616,c_16])).

tff(c_106,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_11,B_57] :
      ( r2_hidden('#skF_3'(A_11),B_57)
      | ~ r1_tarski(A_11,B_57)
      | k1_xboole_0 = A_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_620,plain,(
    ! [A_11,B_57] :
      ( r2_hidden('#skF_3'(A_11),B_57)
      | ~ r1_tarski(A_11,B_57)
      | A_11 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_118])).

tff(c_622,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | A_11 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_14])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_101,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,B_53)
      | ~ r2_hidden(C_54,A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1088,plain,(
    ! [C_158,B_159,A_160] :
      ( ~ r2_hidden(C_158,B_159)
      | ~ r2_hidden(C_158,A_160)
      | k4_xboole_0(A_160,B_159) != A_160 ) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_1278,plain,(
    ! [A_182,A_183] :
      ( ~ r2_hidden('#skF_3'(A_182),A_183)
      | k4_xboole_0(A_183,A_182) != A_183
      | A_182 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_622,c_1088])).

tff(c_1294,plain,(
    ! [B_185,A_186] :
      ( k4_xboole_0(B_185,A_186) != B_185
      | ~ r1_tarski(A_186,B_185)
      | A_186 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_620,c_1278])).

tff(c_1345,plain,
    ( k4_xboole_0('#skF_6','#skF_5') != '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_1294])).

tff(c_1369,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_1345])).

tff(c_1371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_617,c_1369])).

tff(c_1373,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_615])).

tff(c_1374,plain,(
    ! [A_187,B_188] :
      ( k6_setfam_1(A_187,B_188) = k1_setfam_1(B_188)
      | ~ m1_subset_1(B_188,k1_zfmisc_1(k1_zfmisc_1(A_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1391,plain,(
    k6_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_1374])).

tff(c_1567,plain,(
    ! [A_213,B_214] :
      ( k8_setfam_1(A_213,B_214) = k6_setfam_1(A_213,B_214)
      | k1_xboole_0 = B_214
      | ~ m1_subset_1(B_214,k1_zfmisc_1(k1_zfmisc_1(A_213))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1601,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k6_setfam_1('#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_44,c_1567])).

tff(c_1618,plain,
    ( k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1601])).

tff(c_1619,plain,(
    k8_setfam_1('#skF_4','#skF_6') = k1_setfam_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1373,c_1618])).

tff(c_1390,plain,(
    k6_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1374])).

tff(c_1598,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k6_setfam_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_1567])).

tff(c_1615,plain,
    ( k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_1598])).

tff(c_1616,plain,(
    k8_setfam_1('#skF_4','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_1615])).

tff(c_1623,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_4','#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_40])).

tff(c_1649,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_6'),k1_setfam_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1619,c_1623])).

tff(c_1652,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1649])).

tff(c_1655,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1652])).

tff(c_1657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_1655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:32:40 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.60  
% 3.34/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.34/1.60  
% 3.34/1.60  %Foreground sorts:
% 3.34/1.60  
% 3.34/1.60  
% 3.34/1.60  %Background operators:
% 3.34/1.60  
% 3.34/1.60  
% 3.34/1.60  %Foreground operators:
% 3.34/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.60  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.34/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.34/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.60  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.34/1.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.34/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.34/1.60  
% 3.34/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.34/1.62  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.34/1.62  tff(f_111, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.34/1.62  tff(f_95, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.34/1.62  tff(f_89, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.34/1.62  tff(f_66, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.34/1.62  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.34/1.62  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.34/1.62  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.34/1.62  tff(f_101, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.34/1.62  tff(f_60, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.34/1.62  tff(f_64, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.34/1.62  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.34/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.62  tff(c_95, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.62  tff(c_100, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_95])).
% 3.34/1.62  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.62  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.34/1.62  tff(c_123, plain, (![A_61, C_62, B_63]: (m1_subset_1(A_61, C_62) | ~m1_subset_1(B_63, k1_zfmisc_1(C_62)) | ~r2_hidden(A_61, B_63))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.34/1.62  tff(c_160, plain, (![A_68]: (m1_subset_1(A_68, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_68, '#skF_5'))), inference(resolution, [status(thm)], [c_46, c_123])).
% 3.34/1.62  tff(c_32, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.34/1.62  tff(c_168, plain, (![A_69]: (r1_tarski(A_69, '#skF_4') | ~r2_hidden(A_69, '#skF_5'))), inference(resolution, [status(thm)], [c_160, c_32])).
% 3.34/1.62  tff(c_193, plain, (r1_tarski('#skF_3'('#skF_5'), '#skF_4') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_14, c_168])).
% 3.34/1.62  tff(c_194, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_193])).
% 3.34/1.62  tff(c_301, plain, (![A_81]: (r2_hidden('#skF_3'(A_81), A_81) | A_81='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_14])).
% 3.34/1.62  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.34/1.62  tff(c_195, plain, (![A_70]: (m1_subset_1(A_70, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_70, '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_123])).
% 3.34/1.62  tff(c_202, plain, (![A_70]: (r1_tarski(A_70, '#skF_4') | ~r2_hidden(A_70, '#skF_6'))), inference(resolution, [status(thm)], [c_195, c_32])).
% 3.34/1.62  tff(c_317, plain, (r1_tarski('#skF_3'('#skF_6'), '#skF_4') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_301, c_202])).
% 3.34/1.62  tff(c_321, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_317])).
% 3.34/1.62  tff(c_22, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.34/1.62  tff(c_24, plain, (![A_17]: (k8_setfam_1(A_17, k1_xboole_0)=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.34/1.62  tff(c_48, plain, (![A_17]: (k8_setfam_1(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.34/1.62  tff(c_208, plain, (![A_17]: (k8_setfam_1(A_17, '#skF_5')=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_48])).
% 3.34/1.62  tff(c_327, plain, (![A_17]: (k8_setfam_1(A_17, '#skF_6')=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_321, c_208])).
% 3.34/1.62  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k8_setfam_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.34/1.62  tff(c_218, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_40])).
% 3.34/1.62  tff(c_387, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_327, c_218])).
% 3.34/1.62  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_387])).
% 3.34/1.62  tff(c_392, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_317])).
% 3.34/1.62  tff(c_245, plain, (![A_75, B_76]: (k6_setfam_1(A_75, B_76)=k1_setfam_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k1_zfmisc_1(A_75))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.34/1.62  tff(c_259, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_245])).
% 3.34/1.62  tff(c_26, plain, (![A_17, B_18]: (k8_setfam_1(A_17, B_18)=k6_setfam_1(A_17, B_18) | k1_xboole_0=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.34/1.62  tff(c_515, plain, (![A_104, B_105]: (k8_setfam_1(A_104, B_105)=k6_setfam_1(A_104, B_105) | B_105='#skF_5' | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_26])).
% 3.34/1.62  tff(c_546, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_44, c_515])).
% 3.34/1.62  tff(c_558, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_259, c_546])).
% 3.34/1.62  tff(c_559, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_392, c_558])).
% 3.34/1.62  tff(c_560, plain, (~r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_218])).
% 3.34/1.62  tff(c_28, plain, (![A_19, B_20]: (m1_subset_1(k8_setfam_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.34/1.62  tff(c_564, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_559, c_28])).
% 3.34/1.62  tff(c_568, plain, (m1_subset_1(k1_setfam_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_564])).
% 3.34/1.62  tff(c_574, plain, (r1_tarski(k1_setfam_1('#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_568, c_32])).
% 3.34/1.62  tff(c_579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_560, c_574])).
% 3.34/1.62  tff(c_581, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_193])).
% 3.34/1.62  tff(c_42, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.34/1.62  tff(c_38, plain, (![B_29, A_28]: (r1_tarski(k1_setfam_1(B_29), k1_setfam_1(A_28)) | k1_xboole_0=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.34/1.62  tff(c_582, plain, (![A_106]: (m1_subset_1(A_106, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_106, '#skF_6'))), inference(resolution, [status(thm)], [c_44, c_123])).
% 3.34/1.62  tff(c_590, plain, (![A_107]: (r1_tarski(A_107, '#skF_4') | ~r2_hidden(A_107, '#skF_6'))), inference(resolution, [status(thm)], [c_582, c_32])).
% 3.34/1.62  tff(c_615, plain, (r1_tarski('#skF_3'('#skF_6'), '#skF_4') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_14, c_590])).
% 3.34/1.62  tff(c_616, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_615])).
% 3.34/1.62  tff(c_617, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_581])).
% 3.34/1.62  tff(c_16, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.34/1.62  tff(c_625, plain, (![A_13]: (k4_xboole_0('#skF_6', A_13)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_616, c_16])).
% 3.34/1.62  tff(c_106, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.62  tff(c_118, plain, (![A_11, B_57]: (r2_hidden('#skF_3'(A_11), B_57) | ~r1_tarski(A_11, B_57) | k1_xboole_0=A_11)), inference(resolution, [status(thm)], [c_14, c_106])).
% 3.34/1.62  tff(c_620, plain, (![A_11, B_57]: (r2_hidden('#skF_3'(A_11), B_57) | ~r1_tarski(A_11, B_57) | A_11='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_118])).
% 3.34/1.62  tff(c_622, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | A_11='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_616, c_14])).
% 3.34/1.62  tff(c_20, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.62  tff(c_101, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, B_53) | ~r2_hidden(C_54, A_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.34/1.62  tff(c_1088, plain, (![C_158, B_159, A_160]: (~r2_hidden(C_158, B_159) | ~r2_hidden(C_158, A_160) | k4_xboole_0(A_160, B_159)!=A_160)), inference(resolution, [status(thm)], [c_20, c_101])).
% 3.34/1.62  tff(c_1278, plain, (![A_182, A_183]: (~r2_hidden('#skF_3'(A_182), A_183) | k4_xboole_0(A_183, A_182)!=A_183 | A_182='#skF_6')), inference(resolution, [status(thm)], [c_622, c_1088])).
% 3.34/1.62  tff(c_1294, plain, (![B_185, A_186]: (k4_xboole_0(B_185, A_186)!=B_185 | ~r1_tarski(A_186, B_185) | A_186='#skF_6')), inference(resolution, [status(thm)], [c_620, c_1278])).
% 3.34/1.62  tff(c_1345, plain, (k4_xboole_0('#skF_6', '#skF_5')!='#skF_6' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_42, c_1294])).
% 3.34/1.62  tff(c_1369, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_625, c_1345])).
% 3.34/1.62  tff(c_1371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_617, c_1369])).
% 3.34/1.62  tff(c_1373, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_615])).
% 3.34/1.62  tff(c_1374, plain, (![A_187, B_188]: (k6_setfam_1(A_187, B_188)=k1_setfam_1(B_188) | ~m1_subset_1(B_188, k1_zfmisc_1(k1_zfmisc_1(A_187))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.34/1.62  tff(c_1391, plain, (k6_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_1374])).
% 3.34/1.62  tff(c_1567, plain, (![A_213, B_214]: (k8_setfam_1(A_213, B_214)=k6_setfam_1(A_213, B_214) | k1_xboole_0=B_214 | ~m1_subset_1(B_214, k1_zfmisc_1(k1_zfmisc_1(A_213))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.34/1.62  tff(c_1601, plain, (k8_setfam_1('#skF_4', '#skF_6')=k6_setfam_1('#skF_4', '#skF_6') | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_44, c_1567])).
% 3.34/1.62  tff(c_1618, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_1601])).
% 3.34/1.62  tff(c_1619, plain, (k8_setfam_1('#skF_4', '#skF_6')=k1_setfam_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1373, c_1618])).
% 3.34/1.62  tff(c_1390, plain, (k6_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1374])).
% 3.34/1.62  tff(c_1598, plain, (k8_setfam_1('#skF_4', '#skF_5')=k6_setfam_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_1567])).
% 3.34/1.62  tff(c_1615, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_1598])).
% 3.34/1.62  tff(c_1616, plain, (k8_setfam_1('#skF_4', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_581, c_1615])).
% 3.34/1.62  tff(c_1623, plain, (~r1_tarski(k8_setfam_1('#skF_4', '#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_40])).
% 3.34/1.62  tff(c_1649, plain, (~r1_tarski(k1_setfam_1('#skF_6'), k1_setfam_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1619, c_1623])).
% 3.34/1.62  tff(c_1652, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_38, c_1649])).
% 3.34/1.62  tff(c_1655, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1652])).
% 3.34/1.62  tff(c_1657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_581, c_1655])).
% 3.34/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.62  
% 3.34/1.62  Inference rules
% 3.34/1.62  ----------------------
% 3.34/1.62  #Ref     : 0
% 3.34/1.62  #Sup     : 348
% 3.34/1.62  #Fact    : 0
% 3.34/1.62  #Define  : 0
% 3.34/1.62  #Split   : 4
% 3.34/1.62  #Chain   : 0
% 3.34/1.62  #Close   : 0
% 3.34/1.62  
% 3.34/1.62  Ordering : KBO
% 3.34/1.62  
% 3.34/1.62  Simplification rules
% 3.34/1.62  ----------------------
% 3.34/1.62  #Subsume      : 17
% 3.34/1.62  #Demod        : 121
% 3.34/1.62  #Tautology    : 102
% 3.34/1.62  #SimpNegUnit  : 10
% 3.34/1.62  #BackRed      : 38
% 3.34/1.62  
% 3.34/1.62  #Partial instantiations: 0
% 3.34/1.62  #Strategies tried      : 1
% 3.34/1.62  
% 3.34/1.62  Timing (in seconds)
% 3.34/1.62  ----------------------
% 3.34/1.62  Preprocessing        : 0.32
% 3.34/1.62  Parsing              : 0.17
% 3.34/1.62  CNF conversion       : 0.02
% 3.34/1.62  Main loop            : 0.51
% 3.34/1.63  Inferencing          : 0.19
% 3.34/1.63  Reduction            : 0.15
% 3.34/1.63  Demodulation         : 0.10
% 3.34/1.63  BG Simplification    : 0.03
% 3.34/1.63  Subsumption          : 0.10
% 3.34/1.63  Abstraction          : 0.03
% 3.34/1.63  MUC search           : 0.00
% 3.34/1.63  Cooper               : 0.00
% 3.34/1.63  Total                : 0.87
% 3.34/1.63  Index Insertion      : 0.00
% 3.34/1.63  Index Deletion       : 0.00
% 3.34/1.63  Index Matching       : 0.00
% 3.34/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
