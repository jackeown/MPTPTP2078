%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:20 EST 2020

% Result     : Theorem 7.92s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 418 expanded)
%              Number of leaves         :   32 ( 161 expanded)
%              Depth                    :   17
%              Number of atoms          :  184 (1231 expanded)
%              Number of equality atoms :   56 ( 274 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_81,plain,(
    ! [C_48,A_49,B_50] :
      ( v1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_81])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_30,plain,(
    ! [A_26] :
      ( r2_hidden('#skF_1'(A_26),A_26)
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_151,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(k4_tarski(B_85,k1_funct_1(A_86,B_85)),A_86)
      | ~ r2_hidden(B_85,k1_relat_1(A_86))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [C_17,A_14,B_15] :
      ( r2_hidden(C_17,A_14)
      | ~ r2_hidden(C_17,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_227,plain,(
    ! [B_124,A_125,A_126] :
      ( r2_hidden(k4_tarski(B_124,k1_funct_1(A_125,B_124)),A_126)
      | ~ m1_subset_1(A_125,k1_zfmisc_1(A_126))
      | ~ r2_hidden(B_124,k1_relat_1(A_125))
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(resolution,[status(thm)],[c_151,c_18])).

tff(c_14,plain,(
    ! [C_10,A_8,B_9,D_11] :
      ( C_10 = A_8
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(k1_tarski(C_10),D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7696,plain,(
    ! [C_728,B_729,A_730,D_731] :
      ( C_728 = B_729
      | ~ m1_subset_1(A_730,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_728),D_731)))
      | ~ r2_hidden(B_729,k1_relat_1(A_730))
      | ~ v1_funct_1(A_730)
      | ~ v1_relat_1(A_730) ) ),
    inference(resolution,[status(thm)],[c_227,c_14])).

tff(c_7698,plain,(
    ! [B_729] :
      ( B_729 = '#skF_2'
      | ~ r2_hidden(B_729,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_7696])).

tff(c_7703,plain,(
    ! [B_735] :
      ( B_735 = '#skF_2'
      | ~ r2_hidden(B_735,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46,c_7698])).

tff(c_7730,plain,
    ( '#skF_1'(k1_relat_1('#skF_4')) = '#skF_2'
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_7703])).

tff(c_7760,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7730])).

tff(c_26,plain,(
    ! [A_18,B_21] :
      ( k1_funct_1(A_18,B_21) = k1_xboole_0
      | r2_hidden(B_21,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7773,plain,(
    ! [B_21] :
      ( k1_funct_1('#skF_4',B_21) = k1_xboole_0
      | r2_hidden(B_21,k1_xboole_0)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7760,c_26])).

tff(c_7783,plain,(
    ! [B_21] :
      ( k1_funct_1('#skF_4',B_21) = k1_xboole_0
      | r2_hidden(B_21,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46,c_7773])).

tff(c_12,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(k1_tarski(C_10),D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7897,plain,(
    ! [A_760,B_761,D_762,C_763] :
      ( r2_hidden(k1_funct_1(A_760,B_761),D_762)
      | ~ m1_subset_1(A_760,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_763),D_762)))
      | ~ r2_hidden(B_761,k1_relat_1(A_760))
      | ~ v1_funct_1(A_760)
      | ~ v1_relat_1(A_760) ) ),
    inference(resolution,[status(thm)],[c_227,c_12])).

tff(c_7899,plain,(
    ! [B_761] :
      ( r2_hidden(k1_funct_1('#skF_4',B_761),'#skF_3')
      | ~ r2_hidden(B_761,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_7897])).

tff(c_7903,plain,(
    ! [B_764] :
      ( r2_hidden(k1_funct_1('#skF_4',B_764),'#skF_3')
      | ~ r2_hidden(B_764,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46,c_7760,c_7899])).

tff(c_38,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7926,plain,(
    ~ r2_hidden('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_7903,c_38])).

tff(c_7930,plain,(
    k1_funct_1('#skF_4','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_7783,c_7926])).

tff(c_7931,plain,(
    ~ r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7930,c_38])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),B_43) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [A_42] : k1_tarski(A_42) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_7715,plain,(
    ! [B_21] :
      ( B_21 = '#skF_2'
      | k1_funct_1('#skF_4',B_21) = k1_xboole_0
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_7703])).

tff(c_7728,plain,(
    ! [B_21] :
      ( B_21 = '#skF_2'
      | k1_funct_1('#skF_4',B_21) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46,c_7715])).

tff(c_206,plain,(
    ! [D_112,C_113,B_114,A_115] :
      ( r2_hidden(k1_funct_1(D_112,C_113),B_114)
      | k1_xboole_0 = B_114
      | ~ r2_hidden(C_113,A_115)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114)))
      | ~ v1_funct_2(D_112,A_115,B_114)
      | ~ v1_funct_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_7967,plain,(
    ! [D_765,A_766,B_767] :
      ( r2_hidden(k1_funct_1(D_765,'#skF_1'(A_766)),B_767)
      | k1_xboole_0 = B_767
      | ~ m1_subset_1(D_765,k1_zfmisc_1(k2_zfmisc_1(A_766,B_767)))
      | ~ v1_funct_2(D_765,A_766,B_767)
      | ~ v1_funct_1(D_765)
      | k1_xboole_0 = A_766 ) ),
    inference(resolution,[status(thm)],[c_30,c_206])).

tff(c_7990,plain,(
    ! [B_767,A_766] :
      ( r2_hidden(k1_xboole_0,B_767)
      | k1_xboole_0 = B_767
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_766,B_767)))
      | ~ v1_funct_2('#skF_4',A_766,B_767)
      | ~ v1_funct_1('#skF_4')
      | k1_xboole_0 = A_766
      | '#skF_1'(A_766) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7728,c_7967])).

tff(c_8131,plain,(
    ! [B_789,A_790] :
      ( r2_hidden(k1_xboole_0,B_789)
      | k1_xboole_0 = B_789
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_790,B_789)))
      | ~ v1_funct_2('#skF_4',A_790,B_789)
      | k1_xboole_0 = A_790
      | '#skF_1'(A_790) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7990])).

tff(c_8134,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | k1_tarski('#skF_2') = k1_xboole_0
    | '#skF_1'(k1_tarski('#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_8131])).

tff(c_8137,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_2') = k1_xboole_0
    | '#skF_1'(k1_tarski('#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8134])).

tff(c_8138,plain,(
    '#skF_1'(k1_tarski('#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_40,c_7931,c_8137])).

tff(c_224,plain,(
    ! [D_112,A_26,B_114] :
      ( r2_hidden(k1_funct_1(D_112,'#skF_1'(A_26)),B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_26,B_114)))
      | ~ v1_funct_2(D_112,A_26,B_114)
      | ~ v1_funct_1(D_112)
      | k1_xboole_0 = A_26 ) ),
    inference(resolution,[status(thm)],[c_30,c_206])).

tff(c_8142,plain,(
    ! [D_112,B_114] :
      ( r2_hidden(k1_funct_1(D_112,'#skF_2'),B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_114)))
      | ~ v1_funct_2(D_112,k1_tarski('#skF_2'),B_114)
      | ~ v1_funct_1(D_112)
      | k1_tarski('#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8138,c_224])).

tff(c_8326,plain,(
    ! [D_803,B_804] :
      ( r2_hidden(k1_funct_1(D_803,'#skF_2'),B_804)
      | k1_xboole_0 = B_804
      | ~ m1_subset_1(D_803,k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),B_804)))
      | ~ v1_funct_2(D_803,k1_tarski('#skF_2'),B_804)
      | ~ v1_funct_1(D_803) ) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_8142])).

tff(c_8329,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_8326])).

tff(c_8332,plain,
    ( r2_hidden(k1_xboole_0,'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_7930,c_8329])).

tff(c_8334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_7931,c_8332])).

tff(c_8336,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7730])).

tff(c_8335,plain,(
    '#skF_1'(k1_relat_1('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7730])).

tff(c_8368,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8335,c_30])).

tff(c_8386,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_8336,c_8368])).

tff(c_8494,plain,(
    ! [A_836,B_837,D_838,C_839] :
      ( r2_hidden(k1_funct_1(A_836,B_837),D_838)
      | ~ m1_subset_1(A_836,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_839),D_838)))
      | ~ r2_hidden(B_837,k1_relat_1(A_836))
      | ~ v1_funct_1(A_836)
      | ~ v1_relat_1(A_836) ) ),
    inference(resolution,[status(thm)],[c_227,c_12])).

tff(c_8496,plain,(
    ! [B_837] :
      ( r2_hidden(k1_funct_1('#skF_4',B_837),'#skF_3')
      | ~ r2_hidden(B_837,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_8494])).

tff(c_8500,plain,(
    ! [B_840] :
      ( r2_hidden(k1_funct_1('#skF_4',B_840),'#skF_3')
      | ~ r2_hidden(B_840,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_46,c_8496])).

tff(c_8511,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8500,c_38])).

tff(c_8526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8386,c_8511])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:36:07 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.92/2.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/2.69  
% 7.92/2.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.92/2.69  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 7.92/2.69  
% 7.92/2.69  %Foreground sorts:
% 7.92/2.69  
% 7.92/2.69  
% 7.92/2.69  %Background operators:
% 7.92/2.69  
% 7.92/2.69  
% 7.92/2.69  %Foreground operators:
% 7.92/2.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.92/2.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.92/2.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.92/2.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.92/2.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.92/2.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.92/2.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.92/2.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.92/2.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.92/2.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.92/2.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.92/2.69  tff('#skF_2', type, '#skF_2': $i).
% 7.92/2.69  tff('#skF_3', type, '#skF_3': $i).
% 7.92/2.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.92/2.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.92/2.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.92/2.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.92/2.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.92/2.69  tff('#skF_4', type, '#skF_4': $i).
% 7.92/2.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.92/2.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.92/2.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.92/2.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.92/2.69  
% 8.03/2.71  tff(f_111, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 8.03/2.71  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.03/2.71  tff(f_87, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 8.03/2.71  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 8.03/2.71  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 8.03/2.71  tff(f_39, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 8.03/2.71  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 8.03/2.71  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 8.03/2.71  tff(f_99, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 8.03/2.71  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.03/2.71  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.03/2.71  tff(c_81, plain, (![C_48, A_49, B_50]: (v1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.03/2.71  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_81])).
% 8.03/2.71  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.03/2.71  tff(c_30, plain, (![A_26]: (r2_hidden('#skF_1'(A_26), A_26) | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.03/2.71  tff(c_151, plain, (![B_85, A_86]: (r2_hidden(k4_tarski(B_85, k1_funct_1(A_86, B_85)), A_86) | ~r2_hidden(B_85, k1_relat_1(A_86)) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.03/2.71  tff(c_18, plain, (![C_17, A_14, B_15]: (r2_hidden(C_17, A_14) | ~r2_hidden(C_17, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.03/2.71  tff(c_227, plain, (![B_124, A_125, A_126]: (r2_hidden(k4_tarski(B_124, k1_funct_1(A_125, B_124)), A_126) | ~m1_subset_1(A_125, k1_zfmisc_1(A_126)) | ~r2_hidden(B_124, k1_relat_1(A_125)) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(resolution, [status(thm)], [c_151, c_18])).
% 8.03/2.71  tff(c_14, plain, (![C_10, A_8, B_9, D_11]: (C_10=A_8 | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(k1_tarski(C_10), D_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.71  tff(c_7696, plain, (![C_728, B_729, A_730, D_731]: (C_728=B_729 | ~m1_subset_1(A_730, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_728), D_731))) | ~r2_hidden(B_729, k1_relat_1(A_730)) | ~v1_funct_1(A_730) | ~v1_relat_1(A_730))), inference(resolution, [status(thm)], [c_227, c_14])).
% 8.03/2.71  tff(c_7698, plain, (![B_729]: (B_729='#skF_2' | ~r2_hidden(B_729, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_7696])).
% 8.03/2.71  tff(c_7703, plain, (![B_735]: (B_735='#skF_2' | ~r2_hidden(B_735, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46, c_7698])).
% 8.03/2.71  tff(c_7730, plain, ('#skF_1'(k1_relat_1('#skF_4'))='#skF_2' | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_7703])).
% 8.03/2.71  tff(c_7760, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7730])).
% 8.03/2.71  tff(c_26, plain, (![A_18, B_21]: (k1_funct_1(A_18, B_21)=k1_xboole_0 | r2_hidden(B_21, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.03/2.71  tff(c_7773, plain, (![B_21]: (k1_funct_1('#skF_4', B_21)=k1_xboole_0 | r2_hidden(B_21, k1_xboole_0) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7760, c_26])).
% 8.03/2.71  tff(c_7783, plain, (![B_21]: (k1_funct_1('#skF_4', B_21)=k1_xboole_0 | r2_hidden(B_21, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46, c_7773])).
% 8.03/2.71  tff(c_12, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(k1_tarski(C_10), D_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.71  tff(c_7897, plain, (![A_760, B_761, D_762, C_763]: (r2_hidden(k1_funct_1(A_760, B_761), D_762) | ~m1_subset_1(A_760, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_763), D_762))) | ~r2_hidden(B_761, k1_relat_1(A_760)) | ~v1_funct_1(A_760) | ~v1_relat_1(A_760))), inference(resolution, [status(thm)], [c_227, c_12])).
% 8.03/2.71  tff(c_7899, plain, (![B_761]: (r2_hidden(k1_funct_1('#skF_4', B_761), '#skF_3') | ~r2_hidden(B_761, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_7897])).
% 8.03/2.71  tff(c_7903, plain, (![B_764]: (r2_hidden(k1_funct_1('#skF_4', B_764), '#skF_3') | ~r2_hidden(B_764, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46, c_7760, c_7899])).
% 8.03/2.71  tff(c_38, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.03/2.71  tff(c_7926, plain, (~r2_hidden('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_7903, c_38])).
% 8.03/2.71  tff(c_7930, plain, (k1_funct_1('#skF_4', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_7783, c_7926])).
% 8.03/2.71  tff(c_7931, plain, (~r2_hidden(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7930, c_38])).
% 8.03/2.71  tff(c_44, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.03/2.71  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.03/2.71  tff(c_65, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.03/2.71  tff(c_69, plain, (![A_42]: (k1_tarski(A_42)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_65])).
% 8.03/2.71  tff(c_7715, plain, (![B_21]: (B_21='#skF_2' | k1_funct_1('#skF_4', B_21)=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_7703])).
% 8.03/2.71  tff(c_7728, plain, (![B_21]: (B_21='#skF_2' | k1_funct_1('#skF_4', B_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46, c_7715])).
% 8.03/2.71  tff(c_206, plain, (![D_112, C_113, B_114, A_115]: (r2_hidden(k1_funct_1(D_112, C_113), B_114) | k1_xboole_0=B_114 | ~r2_hidden(C_113, A_115) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))) | ~v1_funct_2(D_112, A_115, B_114) | ~v1_funct_1(D_112))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.03/2.71  tff(c_7967, plain, (![D_765, A_766, B_767]: (r2_hidden(k1_funct_1(D_765, '#skF_1'(A_766)), B_767) | k1_xboole_0=B_767 | ~m1_subset_1(D_765, k1_zfmisc_1(k2_zfmisc_1(A_766, B_767))) | ~v1_funct_2(D_765, A_766, B_767) | ~v1_funct_1(D_765) | k1_xboole_0=A_766)), inference(resolution, [status(thm)], [c_30, c_206])).
% 8.03/2.71  tff(c_7990, plain, (![B_767, A_766]: (r2_hidden(k1_xboole_0, B_767) | k1_xboole_0=B_767 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_766, B_767))) | ~v1_funct_2('#skF_4', A_766, B_767) | ~v1_funct_1('#skF_4') | k1_xboole_0=A_766 | '#skF_1'(A_766)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7728, c_7967])).
% 8.03/2.71  tff(c_8131, plain, (![B_789, A_790]: (r2_hidden(k1_xboole_0, B_789) | k1_xboole_0=B_789 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_790, B_789))) | ~v1_funct_2('#skF_4', A_790, B_789) | k1_xboole_0=A_790 | '#skF_1'(A_790)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_7990])).
% 8.03/2.71  tff(c_8134, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | k1_tarski('#skF_2')=k1_xboole_0 | '#skF_1'(k1_tarski('#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_42, c_8131])).
% 8.03/2.71  tff(c_8137, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3' | k1_tarski('#skF_2')=k1_xboole_0 | '#skF_1'(k1_tarski('#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8134])).
% 8.03/2.71  tff(c_8138, plain, ('#skF_1'(k1_tarski('#skF_2'))='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_69, c_40, c_7931, c_8137])).
% 8.03/2.71  tff(c_224, plain, (![D_112, A_26, B_114]: (r2_hidden(k1_funct_1(D_112, '#skF_1'(A_26)), B_114) | k1_xboole_0=B_114 | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_26, B_114))) | ~v1_funct_2(D_112, A_26, B_114) | ~v1_funct_1(D_112) | k1_xboole_0=A_26)), inference(resolution, [status(thm)], [c_30, c_206])).
% 8.03/2.71  tff(c_8142, plain, (![D_112, B_114]: (r2_hidden(k1_funct_1(D_112, '#skF_2'), B_114) | k1_xboole_0=B_114 | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_114))) | ~v1_funct_2(D_112, k1_tarski('#skF_2'), B_114) | ~v1_funct_1(D_112) | k1_tarski('#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8138, c_224])).
% 8.03/2.71  tff(c_8326, plain, (![D_803, B_804]: (r2_hidden(k1_funct_1(D_803, '#skF_2'), B_804) | k1_xboole_0=B_804 | ~m1_subset_1(D_803, k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), B_804))) | ~v1_funct_2(D_803, k1_tarski('#skF_2'), B_804) | ~v1_funct_1(D_803))), inference(negUnitSimplification, [status(thm)], [c_69, c_8142])).
% 8.03/2.71  tff(c_8329, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3') | k1_xboole_0='#skF_3' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_8326])).
% 8.03/2.71  tff(c_8332, plain, (r2_hidden(k1_xboole_0, '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_7930, c_8329])).
% 8.03/2.71  tff(c_8334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_7931, c_8332])).
% 8.03/2.71  tff(c_8336, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_7730])).
% 8.03/2.71  tff(c_8335, plain, ('#skF_1'(k1_relat_1('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_7730])).
% 8.03/2.71  tff(c_8368, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | k1_relat_1('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_8335, c_30])).
% 8.03/2.71  tff(c_8386, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_8336, c_8368])).
% 8.03/2.71  tff(c_8494, plain, (![A_836, B_837, D_838, C_839]: (r2_hidden(k1_funct_1(A_836, B_837), D_838) | ~m1_subset_1(A_836, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_839), D_838))) | ~r2_hidden(B_837, k1_relat_1(A_836)) | ~v1_funct_1(A_836) | ~v1_relat_1(A_836))), inference(resolution, [status(thm)], [c_227, c_12])).
% 8.03/2.71  tff(c_8496, plain, (![B_837]: (r2_hidden(k1_funct_1('#skF_4', B_837), '#skF_3') | ~r2_hidden(B_837, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_8494])).
% 8.03/2.71  tff(c_8500, plain, (![B_840]: (r2_hidden(k1_funct_1('#skF_4', B_840), '#skF_3') | ~r2_hidden(B_840, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_46, c_8496])).
% 8.03/2.71  tff(c_8511, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_8500, c_38])).
% 8.03/2.71  tff(c_8526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8386, c_8511])).
% 8.03/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/2.71  
% 8.03/2.71  Inference rules
% 8.03/2.71  ----------------------
% 8.03/2.71  #Ref     : 0
% 8.03/2.71  #Sup     : 1795
% 8.03/2.71  #Fact    : 1
% 8.03/2.71  #Define  : 0
% 8.03/2.71  #Split   : 51
% 8.03/2.71  #Chain   : 0
% 8.03/2.71  #Close   : 0
% 8.03/2.71  
% 8.03/2.71  Ordering : KBO
% 8.03/2.71  
% 8.03/2.71  Simplification rules
% 8.03/2.71  ----------------------
% 8.03/2.71  #Subsume      : 382
% 8.03/2.71  #Demod        : 1365
% 8.03/2.71  #Tautology    : 318
% 8.03/2.71  #SimpNegUnit  : 366
% 8.03/2.71  #BackRed      : 378
% 8.03/2.71  
% 8.03/2.71  #Partial instantiations: 0
% 8.03/2.71  #Strategies tried      : 1
% 8.03/2.71  
% 8.03/2.71  Timing (in seconds)
% 8.03/2.71  ----------------------
% 8.03/2.71  Preprocessing        : 0.33
% 8.03/2.71  Parsing              : 0.18
% 8.03/2.71  CNF conversion       : 0.02
% 8.03/2.71  Main loop            : 1.61
% 8.03/2.71  Inferencing          : 0.49
% 8.03/2.71  Reduction            : 0.49
% 8.03/2.71  Demodulation         : 0.30
% 8.03/2.71  BG Simplification    : 0.07
% 8.03/2.71  Subsumption          : 0.41
% 8.03/2.71  Abstraction          : 0.08
% 8.03/2.71  MUC search           : 0.00
% 8.03/2.71  Cooper               : 0.00
% 8.03/2.71  Total                : 1.97
% 8.03/2.71  Index Insertion      : 0.00
% 8.03/2.71  Index Deletion       : 0.00
% 8.03/2.71  Index Matching       : 0.00
% 8.03/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
