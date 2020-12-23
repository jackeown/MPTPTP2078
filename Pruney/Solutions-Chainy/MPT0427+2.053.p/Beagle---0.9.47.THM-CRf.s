%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:03 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 431 expanded)
%              Number of leaves         :   31 ( 150 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 870 expanded)
%              Number of equality atoms :   53 ( 187 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_516,plain,(
    ! [A_97,C_98,B_99] :
      ( m1_subset_1(A_97,C_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(C_98))
      | ~ r2_hidden(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_543,plain,(
    ! [A_102] :
      ( m1_subset_1(A_102,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_102,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_516])).

tff(c_30,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_551,plain,(
    ! [A_103] :
      ( r1_tarski(A_103,'#skF_3')
      | ~ r2_hidden(A_103,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_543,c_30])).

tff(c_566,plain,
    ( r1_tarski('#skF_2'('#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_551])).

tff(c_591,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_566])).

tff(c_20,plain,(
    ! [A_18] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_602,plain,(
    ! [A_18] : m1_subset_1('#skF_4',k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_20])).

tff(c_22,plain,(
    ! [A_19] :
      ( k8_setfam_1(A_19,k1_xboole_0) = A_19
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    ! [A_19] : k8_setfam_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_601,plain,(
    ! [A_19] : k8_setfam_1(A_19,'#skF_4') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_46])).

tff(c_642,plain,(
    ! [A_108,B_109] :
      ( m1_subset_1(k8_setfam_1(A_108,B_109),k1_zfmisc_1(A_108))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(k1_zfmisc_1(A_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_654,plain,(
    ! [A_19] :
      ( m1_subset_1(A_19,k1_zfmisc_1(A_19))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_642])).

tff(c_1185,plain,(
    ! [A_159] : m1_subset_1(A_159,k1_zfmisc_1(A_159)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_654])).

tff(c_1202,plain,(
    ! [A_159] : r1_tarski(A_159,A_159) ),
    inference(resolution,[status(thm)],[c_1185,c_30])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_567,plain,(
    ! [A_104] :
      ( m1_subset_1(A_104,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_104,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_42,c_516])).

tff(c_575,plain,(
    ! [A_105] :
      ( r1_tarski(A_105,'#skF_3')
      | ~ r2_hidden(A_105,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_567,c_30])).

tff(c_590,plain,
    ( r1_tarski('#skF_2'('#skF_5'),'#skF_3')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8,c_575])).

tff(c_717,plain,
    ( r1_tarski('#skF_2'('#skF_5'),'#skF_3')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_590])).

tff(c_718,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_717])).

tff(c_38,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_632,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_38])).

tff(c_720,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_632])).

tff(c_731,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_720])).

tff(c_1217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_731])).

tff(c_1219,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_717])).

tff(c_329,plain,(
    ! [A_88,B_89] :
      ( k6_setfam_1(A_88,B_89) = k1_setfam_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_346,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_329])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( k8_setfam_1(A_19,B_20) = k6_setfam_1(A_19,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1307,plain,(
    ! [A_170,B_171] :
      ( k8_setfam_1(A_170,B_171) = k6_setfam_1(A_170,B_171)
      | B_171 = '#skF_4'
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k1_zfmisc_1(A_170))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_24])).

tff(c_1322,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_1307])).

tff(c_1329,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_1322])).

tff(c_1330,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1219,c_1329])).

tff(c_1331,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_632])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k8_setfam_1(A_21,B_22),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1335,plain,
    ( m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1330,c_26])).

tff(c_1339,plain,(
    m1_subset_1(k1_setfam_1('#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1335])).

tff(c_1345,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1339,c_30])).

tff(c_1350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1331,c_1345])).

tff(c_1352,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_566])).

tff(c_40,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_setfam_1(B_31),k1_setfam_1(A_30))
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1388,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_590])).

tff(c_1389,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_1352])).

tff(c_1398,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_8])).

tff(c_59,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_71,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_98,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(B_59,C_58)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_111,plain,(
    ! [A_57,A_18] :
      ( r1_tarski(A_57,A_18)
      | ~ r1_tarski(A_57,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_71,c_98])).

tff(c_1601,plain,(
    ! [A_188,A_189] :
      ( r1_tarski(A_188,A_189)
      | ~ r1_tarski(A_188,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1388,c_111])).

tff(c_1634,plain,(
    ! [A_189] : r1_tarski('#skF_4',A_189) ),
    inference(resolution,[status(thm)],[c_40,c_1601])).

tff(c_84,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_xboole_0(A_47,k4_xboole_0(C_48,B_49))
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_270,plain,(
    ! [A_85,C_86,B_87] :
      ( k4_xboole_0(A_85,k4_xboole_0(C_86,B_87)) = A_85
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(resolution,[status(thm)],[c_84,c_14])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,k4_xboole_0(C_17,B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4571,plain,(
    ! [A_317,A_318,C_319,B_320] :
      ( r1_xboole_0(A_317,A_318)
      | ~ r1_tarski(A_317,k4_xboole_0(C_319,B_320))
      | ~ r1_tarski(A_318,B_320) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_18])).

tff(c_4750,plain,(
    ! [A_323,B_324] :
      ( r1_xboole_0('#skF_4',A_323)
      | ~ r1_tarski(A_323,B_324) ) ),
    inference(resolution,[status(thm)],[c_1634,c_4571])).

tff(c_4825,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1634,c_4750])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4891,plain,(
    ! [C_331] : ~ r2_hidden(C_331,'#skF_4') ),
    inference(resolution,[status(thm)],[c_4825,c_2])).

tff(c_4895,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1398,c_4891])).

tff(c_4907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1389,c_4895])).

tff(c_4909,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_590])).

tff(c_5151,plain,(
    ! [A_346,B_347] :
      ( k8_setfam_1(A_346,B_347) = k6_setfam_1(A_346,B_347)
      | k1_xboole_0 = B_347
      | ~ m1_subset_1(B_347,k1_zfmisc_1(k1_zfmisc_1(A_346))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5173,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_5151])).

tff(c_5187,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_5173])).

tff(c_5188,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_4909,c_5187])).

tff(c_345,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_329])).

tff(c_5170,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_5151])).

tff(c_5184,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_5170])).

tff(c_5185,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1352,c_5184])).

tff(c_5192,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5185,c_38])).

tff(c_5218,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5188,c_5192])).

tff(c_5221,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_5218])).

tff(c_5224,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_5221])).

tff(c_5226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1352,c_5224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.00  
% 5.13/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 5.13/2.00  
% 5.13/2.00  %Foreground sorts:
% 5.13/2.00  
% 5.13/2.00  
% 5.13/2.00  %Background operators:
% 5.13/2.00  
% 5.13/2.00  
% 5.13/2.00  %Foreground operators:
% 5.13/2.00  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.13/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.13/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.13/2.00  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 5.13/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.13/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.13/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.13/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.13/2.00  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 5.13/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/2.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.13/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/2.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.13/2.00  
% 5.13/2.02  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.13/2.02  tff(f_114, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 5.13/2.02  tff(f_98, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 5.13/2.02  tff(f_92, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.13/2.02  tff(f_69, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.13/2.02  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 5.13/2.02  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 5.13/2.02  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 5.13/2.02  tff(f_104, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 5.13/2.02  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.13/2.02  tff(f_67, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.13/2.02  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.13/2.02  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.13/2.02  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.13/2.02  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.13/2.02  tff(c_516, plain, (![A_97, C_98, B_99]: (m1_subset_1(A_97, C_98) | ~m1_subset_1(B_99, k1_zfmisc_1(C_98)) | ~r2_hidden(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.13/2.02  tff(c_543, plain, (![A_102]: (m1_subset_1(A_102, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_102, '#skF_4'))), inference(resolution, [status(thm)], [c_44, c_516])).
% 5.13/2.02  tff(c_30, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.13/2.02  tff(c_551, plain, (![A_103]: (r1_tarski(A_103, '#skF_3') | ~r2_hidden(A_103, '#skF_4'))), inference(resolution, [status(thm)], [c_543, c_30])).
% 5.13/2.02  tff(c_566, plain, (r1_tarski('#skF_2'('#skF_4'), '#skF_3') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_551])).
% 5.13/2.02  tff(c_591, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_566])).
% 5.13/2.02  tff(c_20, plain, (![A_18]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.13/2.02  tff(c_602, plain, (![A_18]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_591, c_20])).
% 5.13/2.02  tff(c_22, plain, (![A_19]: (k8_setfam_1(A_19, k1_xboole_0)=A_19 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.13/2.02  tff(c_46, plain, (![A_19]: (k8_setfam_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 5.13/2.02  tff(c_601, plain, (![A_19]: (k8_setfam_1(A_19, '#skF_4')=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_591, c_46])).
% 5.13/2.02  tff(c_642, plain, (![A_108, B_109]: (m1_subset_1(k8_setfam_1(A_108, B_109), k1_zfmisc_1(A_108)) | ~m1_subset_1(B_109, k1_zfmisc_1(k1_zfmisc_1(A_108))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.13/2.02  tff(c_654, plain, (![A_19]: (m1_subset_1(A_19, k1_zfmisc_1(A_19)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(superposition, [status(thm), theory('equality')], [c_601, c_642])).
% 5.13/2.02  tff(c_1185, plain, (![A_159]: (m1_subset_1(A_159, k1_zfmisc_1(A_159)))), inference(demodulation, [status(thm), theory('equality')], [c_602, c_654])).
% 5.13/2.02  tff(c_1202, plain, (![A_159]: (r1_tarski(A_159, A_159))), inference(resolution, [status(thm)], [c_1185, c_30])).
% 5.13/2.02  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.13/2.02  tff(c_567, plain, (![A_104]: (m1_subset_1(A_104, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_104, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_516])).
% 5.13/2.02  tff(c_575, plain, (![A_105]: (r1_tarski(A_105, '#skF_3') | ~r2_hidden(A_105, '#skF_5'))), inference(resolution, [status(thm)], [c_567, c_30])).
% 5.13/2.02  tff(c_590, plain, (r1_tarski('#skF_2'('#skF_5'), '#skF_3') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8, c_575])).
% 5.13/2.02  tff(c_717, plain, (r1_tarski('#skF_2'('#skF_5'), '#skF_3') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_591, c_590])).
% 5.13/2.02  tff(c_718, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_717])).
% 5.13/2.02  tff(c_38, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.13/2.02  tff(c_632, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_38])).
% 5.13/2.02  tff(c_720, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_718, c_632])).
% 5.13/2.02  tff(c_731, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_720])).
% 5.13/2.02  tff(c_1217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1202, c_731])).
% 5.13/2.02  tff(c_1219, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_717])).
% 5.13/2.02  tff(c_329, plain, (![A_88, B_89]: (k6_setfam_1(A_88, B_89)=k1_setfam_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_88))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.13/2.02  tff(c_346, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_329])).
% 5.13/2.02  tff(c_24, plain, (![A_19, B_20]: (k8_setfam_1(A_19, B_20)=k6_setfam_1(A_19, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.13/2.02  tff(c_1307, plain, (![A_170, B_171]: (k8_setfam_1(A_170, B_171)=k6_setfam_1(A_170, B_171) | B_171='#skF_4' | ~m1_subset_1(B_171, k1_zfmisc_1(k1_zfmisc_1(A_170))))), inference(demodulation, [status(thm), theory('equality')], [c_591, c_24])).
% 5.13/2.02  tff(c_1322, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_42, c_1307])).
% 5.13/2.02  tff(c_1329, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_1322])).
% 5.13/2.02  tff(c_1330, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1219, c_1329])).
% 5.13/2.02  tff(c_1331, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_632])).
% 5.13/2.02  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(k8_setfam_1(A_21, B_22), k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.13/2.02  tff(c_1335, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1330, c_26])).
% 5.13/2.02  tff(c_1339, plain, (m1_subset_1(k1_setfam_1('#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1335])).
% 5.13/2.02  tff(c_1345, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_1339, c_30])).
% 5.13/2.02  tff(c_1350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1331, c_1345])).
% 5.13/2.02  tff(c_1352, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_566])).
% 5.13/2.02  tff(c_40, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.13/2.02  tff(c_36, plain, (![B_31, A_30]: (r1_tarski(k1_setfam_1(B_31), k1_setfam_1(A_30)) | k1_xboole_0=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.13/2.02  tff(c_1388, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_590])).
% 5.13/2.02  tff(c_1389, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_1352])).
% 5.13/2.02  tff(c_1398, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_8])).
% 5.13/2.02  tff(c_59, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.13/2.02  tff(c_71, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(resolution, [status(thm)], [c_20, c_59])).
% 5.13/2.02  tff(c_98, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(B_59, C_58) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.13/2.02  tff(c_111, plain, (![A_57, A_18]: (r1_tarski(A_57, A_18) | ~r1_tarski(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_71, c_98])).
% 5.13/2.02  tff(c_1601, plain, (![A_188, A_189]: (r1_tarski(A_188, A_189) | ~r1_tarski(A_188, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1388, c_111])).
% 5.13/2.02  tff(c_1634, plain, (![A_189]: (r1_tarski('#skF_4', A_189))), inference(resolution, [status(thm)], [c_40, c_1601])).
% 5.13/2.02  tff(c_84, plain, (![A_47, C_48, B_49]: (r1_xboole_0(A_47, k4_xboole_0(C_48, B_49)) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.13/2.02  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.13/2.02  tff(c_270, plain, (![A_85, C_86, B_87]: (k4_xboole_0(A_85, k4_xboole_0(C_86, B_87))=A_85 | ~r1_tarski(A_85, B_87))), inference(resolution, [status(thm)], [c_84, c_14])).
% 5.13/2.02  tff(c_18, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, k4_xboole_0(C_17, B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.13/2.02  tff(c_4571, plain, (![A_317, A_318, C_319, B_320]: (r1_xboole_0(A_317, A_318) | ~r1_tarski(A_317, k4_xboole_0(C_319, B_320)) | ~r1_tarski(A_318, B_320))), inference(superposition, [status(thm), theory('equality')], [c_270, c_18])).
% 5.13/2.02  tff(c_4750, plain, (![A_323, B_324]: (r1_xboole_0('#skF_4', A_323) | ~r1_tarski(A_323, B_324))), inference(resolution, [status(thm)], [c_1634, c_4571])).
% 5.13/2.02  tff(c_4825, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1634, c_4750])).
% 5.13/2.02  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.13/2.02  tff(c_4891, plain, (![C_331]: (~r2_hidden(C_331, '#skF_4'))), inference(resolution, [status(thm)], [c_4825, c_2])).
% 5.13/2.02  tff(c_4895, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1398, c_4891])).
% 5.13/2.02  tff(c_4907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1389, c_4895])).
% 5.13/2.02  tff(c_4909, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_590])).
% 5.13/2.02  tff(c_5151, plain, (![A_346, B_347]: (k8_setfam_1(A_346, B_347)=k6_setfam_1(A_346, B_347) | k1_xboole_0=B_347 | ~m1_subset_1(B_347, k1_zfmisc_1(k1_zfmisc_1(A_346))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.13/2.02  tff(c_5173, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_5151])).
% 5.13/2.02  tff(c_5187, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_5173])).
% 5.13/2.02  tff(c_5188, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_4909, c_5187])).
% 5.13/2.02  tff(c_345, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_329])).
% 5.13/2.02  tff(c_5170, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_5151])).
% 5.13/2.02  tff(c_5184, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_5170])).
% 5.13/2.02  tff(c_5185, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1352, c_5184])).
% 5.13/2.02  tff(c_5192, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5185, c_38])).
% 5.13/2.02  tff(c_5218, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5188, c_5192])).
% 5.13/2.02  tff(c_5221, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_5218])).
% 5.13/2.02  tff(c_5224, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_5221])).
% 5.13/2.02  tff(c_5226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1352, c_5224])).
% 5.13/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.13/2.02  
% 5.13/2.02  Inference rules
% 5.13/2.02  ----------------------
% 5.13/2.02  #Ref     : 0
% 5.13/2.02  #Sup     : 1162
% 5.13/2.02  #Fact    : 0
% 5.13/2.02  #Define  : 0
% 5.13/2.02  #Split   : 9
% 5.13/2.02  #Chain   : 0
% 5.13/2.02  #Close   : 0
% 5.13/2.02  
% 5.13/2.02  Ordering : KBO
% 5.13/2.02  
% 5.13/2.02  Simplification rules
% 5.13/2.02  ----------------------
% 5.13/2.02  #Subsume      : 243
% 5.13/2.02  #Demod        : 552
% 5.13/2.02  #Tautology    : 409
% 5.13/2.02  #SimpNegUnit  : 9
% 5.13/2.02  #BackRed      : 50
% 5.13/2.02  
% 5.13/2.02  #Partial instantiations: 0
% 5.13/2.02  #Strategies tried      : 1
% 5.13/2.02  
% 5.13/2.02  Timing (in seconds)
% 5.13/2.02  ----------------------
% 5.13/2.02  Preprocessing        : 0.33
% 5.13/2.02  Parsing              : 0.18
% 5.13/2.02  CNF conversion       : 0.02
% 5.13/2.02  Main loop            : 0.87
% 5.13/2.02  Inferencing          : 0.30
% 5.13/2.02  Reduction            : 0.29
% 5.13/2.02  Demodulation         : 0.21
% 5.13/2.02  BG Simplification    : 0.03
% 5.13/2.02  Subsumption          : 0.17
% 5.13/2.02  Abstraction          : 0.05
% 5.13/2.02  MUC search           : 0.00
% 5.13/2.02  Cooper               : 0.00
% 5.13/2.02  Total                : 1.24
% 5.13/2.02  Index Insertion      : 0.00
% 5.13/2.02  Index Deletion       : 0.00
% 5.13/2.02  Index Matching       : 0.00
% 5.13/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
