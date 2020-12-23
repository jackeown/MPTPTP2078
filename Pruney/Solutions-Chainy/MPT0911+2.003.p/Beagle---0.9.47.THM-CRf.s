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
% DateTime   : Thu Dec  3 10:10:02 EST 2020

% Result     : Theorem 9.23s
% Output     : CNFRefutation 9.44s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 961 expanded)
%              Number of leaves         :   46 ( 338 expanded)
%              Depth                    :   17
%              Number of atoms          :  266 (2676 expanded)
%              Number of equality atoms :  128 (1028 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_99,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ v1_xboole_0(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_zfmisc_1)).

tff(c_28,plain,(
    ! [A_34,B_35] : v1_relat_1(k2_zfmisc_1(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    m1_subset_1('#skF_12',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_219,plain,(
    ! [B_132,A_133] :
      ( v1_xboole_0(B_132)
      | ~ m1_subset_1(B_132,A_133)
      | ~ v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_239,plain,
    ( v1_xboole_0('#skF_12')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_76,c_219])).

tff(c_240,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [A_136,B_137,C_138] : k2_zfmisc_1(k2_zfmisc_1(A_136,B_137),C_138) = k3_zfmisc_1(A_136,B_137,C_138) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_258,plain,(
    ! [A_136,B_137,C_138] : v1_relat_1(k3_zfmisc_1(A_136,B_137,C_138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_28])).

tff(c_564,plain,(
    ! [A_195,B_196] :
      ( k4_tarski('#skF_5'(A_195,B_196),'#skF_6'(A_195,B_196)) = B_196
      | ~ r2_hidden(B_196,A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_64,plain,(
    ! [A_76,B_77] : k2_mcart_1(k4_tarski(A_76,B_77)) = B_77 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_982,plain,(
    ! [B_264,A_265] :
      ( k2_mcart_1(B_264) = '#skF_6'(A_265,B_264)
      | ~ r2_hidden(B_264,A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_64])).

tff(c_12464,plain,(
    ! [B_687,A_688] :
      ( k2_mcart_1(B_687) = '#skF_6'(A_688,B_687)
      | ~ v1_relat_1(A_688)
      | ~ m1_subset_1(B_687,A_688)
      | v1_xboole_0(A_688) ) ),
    inference(resolution,[status(thm)],[c_14,c_982])).

tff(c_12491,plain,
    ( '#skF_6'(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'),'#skF_12') = k2_mcart_1('#skF_12')
    | ~ v1_relat_1(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_76,c_12464])).

tff(c_12502,plain,
    ( '#skF_6'(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'),'#skF_12') = k2_mcart_1('#skF_12')
    | v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_12491])).

tff(c_12503,plain,(
    '#skF_6'(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'),'#skF_12') = k2_mcart_1('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_12502])).

tff(c_62,plain,(
    ! [A_76,B_77] : k1_mcart_1(k4_tarski(A_76,B_77)) = A_76 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_961,plain,(
    ! [B_262,A_263] :
      ( k1_mcart_1(B_262) = '#skF_5'(A_263,B_262)
      | ~ r2_hidden(B_262,A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_62])).

tff(c_12792,plain,(
    ! [B_702,A_703] :
      ( k1_mcart_1(B_702) = '#skF_5'(A_703,B_702)
      | ~ v1_relat_1(A_703)
      | ~ m1_subset_1(B_702,A_703)
      | v1_xboole_0(A_703) ) ),
    inference(resolution,[status(thm)],[c_14,c_961])).

tff(c_12819,plain,
    ( '#skF_5'(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'),'#skF_12') = k1_mcart_1('#skF_12')
    | ~ v1_relat_1(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_76,c_12792])).

tff(c_12830,plain,
    ( '#skF_5'(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'),'#skF_12') = k1_mcart_1('#skF_12')
    | v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_12819])).

tff(c_12831,plain,(
    '#skF_5'(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'),'#skF_12') = k1_mcart_1('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_12830])).

tff(c_22,plain,(
    ! [A_16,B_31] :
      ( k4_tarski('#skF_5'(A_16,B_31),'#skF_6'(A_16,B_31)) = B_31
      | ~ r2_hidden(B_31,A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12846,plain,
    ( k4_tarski(k1_mcart_1('#skF_12'),'#skF_6'(k3_zfmisc_1('#skF_8','#skF_9','#skF_10'),'#skF_12')) = '#skF_12'
    | ~ r2_hidden('#skF_12',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | ~ v1_relat_1(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12831,c_22])).

tff(c_12852,plain,
    ( k4_tarski(k1_mcart_1('#skF_12'),k2_mcart_1('#skF_12')) = '#skF_12'
    | ~ r2_hidden('#skF_12',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_12503,c_12846])).

tff(c_14916,plain,(
    ~ r2_hidden('#skF_12',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_12852])).

tff(c_14919,plain,
    ( ~ m1_subset_1('#skF_12',k3_zfmisc_1('#skF_8','#skF_9','#skF_10'))
    | v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_14,c_14916])).

tff(c_14922,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_14919])).

tff(c_14924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_14922])).

tff(c_14926,plain,(
    r2_hidden('#skF_12',k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_12852])).

tff(c_32,plain,(
    ! [A_39,B_40,C_41] : k2_zfmisc_1(k2_zfmisc_1(A_39,B_40),C_41) = k3_zfmisc_1(A_39,B_40,C_41) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_331,plain,(
    ! [A_157,B_158,C_159] :
      ( r2_hidden(k1_mcart_1(A_157),B_158)
      | ~ r2_hidden(A_157,k2_zfmisc_1(B_158,C_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_333,plain,(
    ! [A_157,A_39,B_40,C_41] :
      ( r2_hidden(k1_mcart_1(A_157),k2_zfmisc_1(A_39,B_40))
      | ~ r2_hidden(A_157,k3_zfmisc_1(A_39,B_40,C_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_331])).

tff(c_15142,plain,(
    r2_hidden(k1_mcart_1('#skF_12'),k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_14926,c_333])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_844,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k5_mcart_1(A_241,B_242,C_243,D_244) = k1_mcart_1(k1_mcart_1(D_244))
      | ~ m1_subset_1(D_244,k3_zfmisc_1(A_241,B_242,C_243))
      | k1_xboole_0 = C_243
      | k1_xboole_0 = B_242
      | k1_xboole_0 = A_241 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_866,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_12')) = k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_76,c_844])).

tff(c_875,plain,(
    k1_mcart_1(k1_mcart_1('#skF_12')) = k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_68,c_866])).

tff(c_38,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k1_mcart_1(A_46),B_47)
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15240,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_12')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_15142,c_38])).

tff(c_15266,plain,(
    r2_hidden(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_875,c_15240])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,B_15)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15498,plain,(
    m1_subset_1(k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_15266,c_20])).

tff(c_574,plain,(
    ! [B_196,A_195] :
      ( k1_mcart_1(B_196) = '#skF_5'(A_195,B_196)
      | ~ r2_hidden(B_196,A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_62])).

tff(c_15228,plain,
    ( '#skF_5'(k2_zfmisc_1('#skF_8','#skF_9'),k1_mcart_1('#skF_12')) = k1_mcart_1(k1_mcart_1('#skF_12'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_15142,c_574])).

tff(c_15258,plain,(
    '#skF_5'(k2_zfmisc_1('#skF_8','#skF_9'),k1_mcart_1('#skF_12')) = k5_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_875,c_15228])).

tff(c_895,plain,(
    ! [A_251,B_252,C_253,D_254] :
      ( k6_mcart_1(A_251,B_252,C_253,D_254) = k2_mcart_1(k1_mcart_1(D_254))
      | ~ m1_subset_1(D_254,k3_zfmisc_1(A_251,B_252,C_253))
      | k1_xboole_0 = C_253
      | k1_xboole_0 = B_252
      | k1_xboole_0 = A_251 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_917,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_12')) = k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_76,c_895])).

tff(c_926,plain,(
    k2_mcart_1(k1_mcart_1('#skF_12')) = k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_68,c_917])).

tff(c_36,plain,(
    ! [A_46,C_48,B_47] :
      ( r2_hidden(k2_mcart_1(A_46),C_48)
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15242,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_12')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_15142,c_36])).

tff(c_15268,plain,(
    r2_hidden(k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_15242])).

tff(c_15528,plain,(
    m1_subset_1(k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_15268,c_20])).

tff(c_577,plain,(
    ! [B_196,A_195] :
      ( k2_mcart_1(B_196) = '#skF_6'(A_195,B_196)
      | ~ r2_hidden(B_196,A_195)
      | ~ v1_relat_1(A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_64])).

tff(c_15225,plain,
    ( '#skF_6'(k2_zfmisc_1('#skF_8','#skF_9'),k1_mcart_1('#skF_12')) = k2_mcart_1(k1_mcart_1('#skF_12'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_15142,c_577])).

tff(c_15255,plain,(
    '#skF_6'(k2_zfmisc_1('#skF_8','#skF_9'),k1_mcart_1('#skF_12')) = k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_926,c_15225])).

tff(c_292,plain,(
    ! [A_145,C_146,B_147] :
      ( r2_hidden(k2_mcart_1(A_145),C_146)
      | ~ r2_hidden(A_145,k2_zfmisc_1(B_147,C_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_294,plain,(
    ! [A_145,C_41,A_39,B_40] :
      ( r2_hidden(k2_mcart_1(A_145),C_41)
      | ~ r2_hidden(A_145,k3_zfmisc_1(A_39,B_40,C_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_292])).

tff(c_15155,plain,(
    r2_hidden(k2_mcart_1('#skF_12'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_14926,c_294])).

tff(c_15187,plain,(
    m1_subset_1(k2_mcart_1('#skF_12'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_15155,c_20])).

tff(c_776,plain,(
    ! [A_230,B_231,C_232,D_233] :
      ( k7_mcart_1(A_230,B_231,C_232,D_233) = k2_mcart_1(D_233)
      | ~ m1_subset_1(D_233,k3_zfmisc_1(A_230,B_231,C_232))
      | k1_xboole_0 = C_232
      | k1_xboole_0 = B_231
      | k1_xboole_0 = A_230 ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_798,plain,
    ( k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12') = k2_mcart_1('#skF_12')
    | k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_76,c_776])).

tff(c_807,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12') = k2_mcart_1('#skF_12') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_70,c_68,c_798])).

tff(c_66,plain,(
    k7_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12') != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_808,plain,(
    k2_mcart_1('#skF_12') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_66])).

tff(c_14925,plain,(
    k4_tarski(k1_mcart_1('#skF_12'),k2_mcart_1('#skF_12')) = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_12852])).

tff(c_30,plain,(
    ! [A_36,B_37,C_38] : k4_tarski(k4_tarski(A_36,B_37),C_38) = k3_mcart_1(A_36,B_37,C_38) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12388,plain,(
    ! [A_673,B_674,C_675] :
      ( k3_mcart_1('#skF_5'(A_673,B_674),'#skF_6'(A_673,B_674),C_675) = k4_tarski(B_674,C_675)
      | ~ r2_hidden(B_674,A_673)
      | ~ v1_relat_1(A_673) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_30])).

tff(c_74,plain,(
    ! [H_91,F_85,G_89] :
      ( H_91 = '#skF_11'
      | k3_mcart_1(F_85,G_89,H_91) != '#skF_12'
      | ~ m1_subset_1(H_91,'#skF_10')
      | ~ m1_subset_1(G_89,'#skF_9')
      | ~ m1_subset_1(F_85,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_12404,plain,(
    ! [C_675,B_674,A_673] :
      ( C_675 = '#skF_11'
      | k4_tarski(B_674,C_675) != '#skF_12'
      | ~ m1_subset_1(C_675,'#skF_10')
      | ~ m1_subset_1('#skF_6'(A_673,B_674),'#skF_9')
      | ~ m1_subset_1('#skF_5'(A_673,B_674),'#skF_8')
      | ~ r2_hidden(B_674,A_673)
      | ~ v1_relat_1(A_673) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12388,c_74])).

tff(c_14931,plain,(
    ! [A_673] :
      ( k2_mcart_1('#skF_12') = '#skF_11'
      | ~ m1_subset_1(k2_mcart_1('#skF_12'),'#skF_10')
      | ~ m1_subset_1('#skF_6'(A_673,k1_mcart_1('#skF_12')),'#skF_9')
      | ~ m1_subset_1('#skF_5'(A_673,k1_mcart_1('#skF_12')),'#skF_8')
      | ~ r2_hidden(k1_mcart_1('#skF_12'),A_673)
      | ~ v1_relat_1(A_673) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14925,c_12404])).

tff(c_14954,plain,(
    ! [A_673] :
      ( ~ m1_subset_1(k2_mcart_1('#skF_12'),'#skF_10')
      | ~ m1_subset_1('#skF_6'(A_673,k1_mcart_1('#skF_12')),'#skF_9')
      | ~ m1_subset_1('#skF_5'(A_673,k1_mcart_1('#skF_12')),'#skF_8')
      | ~ r2_hidden(k1_mcart_1('#skF_12'),A_673)
      | ~ v1_relat_1(A_673) ) ),
    inference(negUnitSimplification,[status(thm)],[c_808,c_14931])).

tff(c_19886,plain,(
    ! [A_857] :
      ( ~ m1_subset_1('#skF_6'(A_857,k1_mcart_1('#skF_12')),'#skF_9')
      | ~ m1_subset_1('#skF_5'(A_857,k1_mcart_1('#skF_12')),'#skF_8')
      | ~ r2_hidden(k1_mcart_1('#skF_12'),A_857)
      | ~ v1_relat_1(A_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15187,c_14954])).

tff(c_19889,plain,
    ( ~ m1_subset_1(k6_mcart_1('#skF_8','#skF_9','#skF_10','#skF_12'),'#skF_9')
    | ~ m1_subset_1('#skF_5'(k2_zfmisc_1('#skF_8','#skF_9'),k1_mcart_1('#skF_12')),'#skF_8')
    | ~ r2_hidden(k1_mcart_1('#skF_12'),k2_zfmisc_1('#skF_8','#skF_9'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15255,c_19886])).

tff(c_19895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_15142,c_15498,c_15258,c_15528,c_19889])).

tff(c_19896,plain,(
    v1_xboole_0('#skF_12') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_168,plain,(
    ! [A_119] :
      ( r2_hidden('#skF_7'(A_119),A_119)
      | k1_xboole_0 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [A_119] :
      ( ~ v1_xboole_0(A_119)
      | k1_xboole_0 = A_119 ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_19904,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_19896,c_176])).

tff(c_19917,plain,(
    '#skF_8' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_72])).

tff(c_19916,plain,(
    '#skF_9' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_70])).

tff(c_19914,plain,(
    '#skF_10' != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_68])).

tff(c_60,plain,(
    ! [B_73,C_74,D_75] : k4_zfmisc_1(k1_xboole_0,B_73,C_74,D_75) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_19907,plain,(
    ! [B_73,C_74,D_75] : k4_zfmisc_1('#skF_12',B_73,C_74,D_75) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_19904,c_60])).

tff(c_19897,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_19908,plain,(
    ! [A_119] :
      ( ~ v1_xboole_0(A_119)
      | A_119 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_176])).

tff(c_19945,plain,(
    k3_zfmisc_1('#skF_8','#skF_9','#skF_10') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_19897,c_19908])).

tff(c_20138,plain,(
    ! [A_893,B_894,C_895,D_896] : k2_zfmisc_1(k3_zfmisc_1(A_893,B_894,C_895),D_896) = k4_zfmisc_1(A_893,B_894,C_895,D_896) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20190,plain,(
    ! [D_907] : k4_zfmisc_1('#skF_8','#skF_9','#skF_10',D_907) = k2_zfmisc_1('#skF_12',D_907) ),
    inference(superposition,[status(thm),theory(equality)],[c_19945,c_20138])).

tff(c_54,plain,(
    ! [A_72,B_73,C_74] : k4_zfmisc_1(A_72,B_73,C_74,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_19910,plain,(
    ! [A_72,B_73,C_74] : k4_zfmisc_1(A_72,B_73,C_74,'#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_19904,c_54])).

tff(c_20199,plain,(
    k2_zfmisc_1('#skF_12','#skF_12') = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_20190,c_19910])).

tff(c_20283,plain,(
    ! [C_915] : k3_zfmisc_1('#skF_12','#skF_12',C_915) = k2_zfmisc_1('#skF_12',C_915) ),
    inference(superposition,[status(thm),theory(equality)],[c_20199,c_32])).

tff(c_34,plain,(
    ! [A_42,B_43,C_44,D_45] : k2_zfmisc_1(k3_zfmisc_1(A_42,B_43,C_44),D_45) = k4_zfmisc_1(A_42,B_43,C_44,D_45) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20289,plain,(
    ! [C_915,D_45] : k2_zfmisc_1(k2_zfmisc_1('#skF_12',C_915),D_45) = k4_zfmisc_1('#skF_12','#skF_12',C_915,D_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_20283,c_34])).

tff(c_20296,plain,(
    ! [C_915,D_45] : k3_zfmisc_1('#skF_12',C_915,D_45) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19907,c_32,c_20289])).

tff(c_20217,plain,(
    ! [C_41] : k3_zfmisc_1('#skF_12','#skF_12',C_41) = k2_zfmisc_1('#skF_12',C_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_20199,c_32])).

tff(c_20299,plain,(
    ! [C_41] : k2_zfmisc_1('#skF_12',C_41) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20296,c_20217])).

tff(c_20156,plain,(
    ! [D_896] : k4_zfmisc_1('#skF_8','#skF_9','#skF_10',D_896) = k2_zfmisc_1('#skF_12',D_896) ),
    inference(superposition,[status(thm),theory(equality)],[c_19945,c_20138])).

tff(c_20315,plain,(
    ! [D_896] : k4_zfmisc_1('#skF_8','#skF_9','#skF_10',D_896) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20299,c_20156])).

tff(c_52,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( k4_zfmisc_1(A_72,B_73,C_74,D_75) != k1_xboole_0
      | k1_xboole_0 = D_75
      | k1_xboole_0 = C_74
      | k1_xboole_0 = B_73
      | k1_xboole_0 = A_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_20586,plain,(
    ! [A_964,B_965,C_966,D_967] :
      ( k4_zfmisc_1(A_964,B_965,C_966,D_967) != '#skF_12'
      | D_967 = '#skF_12'
      | C_966 = '#skF_12'
      | B_965 = '#skF_12'
      | A_964 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_19904,c_19904,c_19904,c_19904,c_52])).

tff(c_20589,plain,(
    ! [D_896] :
      ( D_896 = '#skF_12'
      | '#skF_10' = '#skF_12'
      | '#skF_9' = '#skF_12'
      | '#skF_8' = '#skF_12' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20315,c_20586])).

tff(c_20613,plain,(
    ! [D_968] : D_968 = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_19917,c_19916,c_19914,c_20589])).

tff(c_20113,plain,(
    ! [A_887,B_888,C_889] : k4_tarski(k4_tarski(A_887,B_888),C_889) = k3_mcart_1(A_887,B_888,C_889) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_5,B_6] : ~ v1_xboole_0(k4_tarski(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20128,plain,(
    ! [A_887,B_888,C_889] : ~ v1_xboole_0(k3_mcart_1(A_887,B_888,C_889)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20113,c_8])).

tff(c_20656,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_20613,c_20128])).

tff(c_20719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19896,c_20656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.23/3.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.45  
% 9.44/3.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.46  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_11 > #skF_1 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5 > #skF_12
% 9.44/3.46  
% 9.44/3.46  %Foreground sorts:
% 9.44/3.46  
% 9.44/3.46  
% 9.44/3.46  %Background operators:
% 9.44/3.46  
% 9.44/3.46  
% 9.44/3.46  %Foreground operators:
% 9.44/3.46  tff('#skF_7', type, '#skF_7': $i > $i).
% 9.44/3.46  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.44/3.46  tff('#skF_4', type, '#skF_4': $i > $i).
% 9.44/3.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.44/3.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.44/3.46  tff('#skF_11', type, '#skF_11': $i).
% 9.44/3.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.44/3.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.44/3.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.44/3.46  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 9.44/3.46  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 9.44/3.46  tff('#skF_10', type, '#skF_10': $i).
% 9.44/3.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.44/3.46  tff('#skF_9', type, '#skF_9': $i).
% 9.44/3.46  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 9.44/3.46  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.44/3.46  tff('#skF_8', type, '#skF_8': $i).
% 9.44/3.46  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 9.44/3.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.44/3.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 9.44/3.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.44/3.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.44/3.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.44/3.46  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 9.44/3.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.44/3.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 9.44/3.46  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 9.44/3.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.44/3.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.44/3.46  tff('#skF_12', type, '#skF_12': $i).
% 9.44/3.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.44/3.46  
% 9.44/3.48  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.44/3.48  tff(f_162, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 9.44/3.48  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.44/3.48  tff(f_75, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.44/3.48  tff(f_69, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 9.44/3.48  tff(f_138, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 9.44/3.48  tff(f_83, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 9.44/3.48  tff(f_119, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 9.44/3.48  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.44/3.48  tff(f_73, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 9.44/3.48  tff(f_99, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 9.44/3.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.44/3.48  tff(f_134, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 9.44/3.48  tff(f_77, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.44/3.48  tff(f_35, axiom, (![A, B]: ~v1_xboole_0(k4_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_zfmisc_1)).
% 9.44/3.48  tff(c_28, plain, (![A_34, B_35]: (v1_relat_1(k2_zfmisc_1(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.44/3.48  tff(c_76, plain, (m1_subset_1('#skF_12', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.44/3.48  tff(c_219, plain, (![B_132, A_133]: (v1_xboole_0(B_132) | ~m1_subset_1(B_132, A_133) | ~v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.44/3.48  tff(c_239, plain, (v1_xboole_0('#skF_12') | ~v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_76, c_219])).
% 9.44/3.48  tff(c_240, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_239])).
% 9.44/3.48  tff(c_14, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.44/3.48  tff(c_250, plain, (![A_136, B_137, C_138]: (k2_zfmisc_1(k2_zfmisc_1(A_136, B_137), C_138)=k3_zfmisc_1(A_136, B_137, C_138))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.44/3.48  tff(c_258, plain, (![A_136, B_137, C_138]: (v1_relat_1(k3_zfmisc_1(A_136, B_137, C_138)))), inference(superposition, [status(thm), theory('equality')], [c_250, c_28])).
% 9.44/3.48  tff(c_564, plain, (![A_195, B_196]: (k4_tarski('#skF_5'(A_195, B_196), '#skF_6'(A_195, B_196))=B_196 | ~r2_hidden(B_196, A_195) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.44/3.48  tff(c_64, plain, (![A_76, B_77]: (k2_mcart_1(k4_tarski(A_76, B_77))=B_77)), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.48  tff(c_982, plain, (![B_264, A_265]: (k2_mcart_1(B_264)='#skF_6'(A_265, B_264) | ~r2_hidden(B_264, A_265) | ~v1_relat_1(A_265))), inference(superposition, [status(thm), theory('equality')], [c_564, c_64])).
% 9.44/3.48  tff(c_12464, plain, (![B_687, A_688]: (k2_mcart_1(B_687)='#skF_6'(A_688, B_687) | ~v1_relat_1(A_688) | ~m1_subset_1(B_687, A_688) | v1_xboole_0(A_688))), inference(resolution, [status(thm)], [c_14, c_982])).
% 9.44/3.48  tff(c_12491, plain, ('#skF_6'(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'), '#skF_12')=k2_mcart_1('#skF_12') | ~v1_relat_1(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_76, c_12464])).
% 9.44/3.48  tff(c_12502, plain, ('#skF_6'(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'), '#skF_12')=k2_mcart_1('#skF_12') | v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_12491])).
% 9.44/3.48  tff(c_12503, plain, ('#skF_6'(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'), '#skF_12')=k2_mcart_1('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_240, c_12502])).
% 9.44/3.48  tff(c_62, plain, (![A_76, B_77]: (k1_mcart_1(k4_tarski(A_76, B_77))=A_76)), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.44/3.48  tff(c_961, plain, (![B_262, A_263]: (k1_mcart_1(B_262)='#skF_5'(A_263, B_262) | ~r2_hidden(B_262, A_263) | ~v1_relat_1(A_263))), inference(superposition, [status(thm), theory('equality')], [c_564, c_62])).
% 9.44/3.48  tff(c_12792, plain, (![B_702, A_703]: (k1_mcart_1(B_702)='#skF_5'(A_703, B_702) | ~v1_relat_1(A_703) | ~m1_subset_1(B_702, A_703) | v1_xboole_0(A_703))), inference(resolution, [status(thm)], [c_14, c_961])).
% 9.44/3.48  tff(c_12819, plain, ('#skF_5'(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'), '#skF_12')=k1_mcart_1('#skF_12') | ~v1_relat_1(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_76, c_12792])).
% 9.44/3.48  tff(c_12830, plain, ('#skF_5'(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'), '#skF_12')=k1_mcart_1('#skF_12') | v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_12819])).
% 9.44/3.48  tff(c_12831, plain, ('#skF_5'(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'), '#skF_12')=k1_mcart_1('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_240, c_12830])).
% 9.44/3.48  tff(c_22, plain, (![A_16, B_31]: (k4_tarski('#skF_5'(A_16, B_31), '#skF_6'(A_16, B_31))=B_31 | ~r2_hidden(B_31, A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.44/3.48  tff(c_12846, plain, (k4_tarski(k1_mcart_1('#skF_12'), '#skF_6'(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'), '#skF_12'))='#skF_12' | ~r2_hidden('#skF_12', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | ~v1_relat_1(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_12831, c_22])).
% 9.44/3.48  tff(c_12852, plain, (k4_tarski(k1_mcart_1('#skF_12'), k2_mcart_1('#skF_12'))='#skF_12' | ~r2_hidden('#skF_12', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_12503, c_12846])).
% 9.44/3.48  tff(c_14916, plain, (~r2_hidden('#skF_12', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_12852])).
% 9.44/3.48  tff(c_14919, plain, (~m1_subset_1('#skF_12', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')) | v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_14, c_14916])).
% 9.44/3.48  tff(c_14922, plain, (v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_14919])).
% 9.44/3.48  tff(c_14924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_14922])).
% 9.44/3.48  tff(c_14926, plain, (r2_hidden('#skF_12', k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_12852])).
% 9.44/3.48  tff(c_32, plain, (![A_39, B_40, C_41]: (k2_zfmisc_1(k2_zfmisc_1(A_39, B_40), C_41)=k3_zfmisc_1(A_39, B_40, C_41))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.44/3.48  tff(c_331, plain, (![A_157, B_158, C_159]: (r2_hidden(k1_mcart_1(A_157), B_158) | ~r2_hidden(A_157, k2_zfmisc_1(B_158, C_159)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.44/3.48  tff(c_333, plain, (![A_157, A_39, B_40, C_41]: (r2_hidden(k1_mcart_1(A_157), k2_zfmisc_1(A_39, B_40)) | ~r2_hidden(A_157, k3_zfmisc_1(A_39, B_40, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_331])).
% 9.44/3.48  tff(c_15142, plain, (r2_hidden(k1_mcart_1('#skF_12'), k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_14926, c_333])).
% 9.44/3.48  tff(c_72, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.44/3.48  tff(c_70, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.44/3.48  tff(c_68, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.44/3.48  tff(c_844, plain, (![A_241, B_242, C_243, D_244]: (k5_mcart_1(A_241, B_242, C_243, D_244)=k1_mcart_1(k1_mcart_1(D_244)) | ~m1_subset_1(D_244, k3_zfmisc_1(A_241, B_242, C_243)) | k1_xboole_0=C_243 | k1_xboole_0=B_242 | k1_xboole_0=A_241)), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.44/3.48  tff(c_866, plain, (k1_mcart_1(k1_mcart_1('#skF_12'))=k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_76, c_844])).
% 9.44/3.48  tff(c_875, plain, (k1_mcart_1(k1_mcart_1('#skF_12'))=k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_68, c_866])).
% 9.44/3.48  tff(c_38, plain, (![A_46, B_47, C_48]: (r2_hidden(k1_mcart_1(A_46), B_47) | ~r2_hidden(A_46, k2_zfmisc_1(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.44/3.48  tff(c_15240, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_12')), '#skF_8')), inference(resolution, [status(thm)], [c_15142, c_38])).
% 9.44/3.48  tff(c_15266, plain, (r2_hidden(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_875, c_15240])).
% 9.44/3.48  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(A_14, B_15) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.44/3.48  tff(c_15498, plain, (m1_subset_1(k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12'), '#skF_8')), inference(resolution, [status(thm)], [c_15266, c_20])).
% 9.44/3.48  tff(c_574, plain, (![B_196, A_195]: (k1_mcart_1(B_196)='#skF_5'(A_195, B_196) | ~r2_hidden(B_196, A_195) | ~v1_relat_1(A_195))), inference(superposition, [status(thm), theory('equality')], [c_564, c_62])).
% 9.44/3.48  tff(c_15228, plain, ('#skF_5'(k2_zfmisc_1('#skF_8', '#skF_9'), k1_mcart_1('#skF_12'))=k1_mcart_1(k1_mcart_1('#skF_12')) | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_15142, c_574])).
% 9.44/3.48  tff(c_15258, plain, ('#skF_5'(k2_zfmisc_1('#skF_8', '#skF_9'), k1_mcart_1('#skF_12'))=k5_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_875, c_15228])).
% 9.44/3.48  tff(c_895, plain, (![A_251, B_252, C_253, D_254]: (k6_mcart_1(A_251, B_252, C_253, D_254)=k2_mcart_1(k1_mcart_1(D_254)) | ~m1_subset_1(D_254, k3_zfmisc_1(A_251, B_252, C_253)) | k1_xboole_0=C_253 | k1_xboole_0=B_252 | k1_xboole_0=A_251)), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.44/3.48  tff(c_917, plain, (k2_mcart_1(k1_mcart_1('#skF_12'))=k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_76, c_895])).
% 9.44/3.48  tff(c_926, plain, (k2_mcart_1(k1_mcart_1('#skF_12'))=k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12')), inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_68, c_917])).
% 9.44/3.48  tff(c_36, plain, (![A_46, C_48, B_47]: (r2_hidden(k2_mcart_1(A_46), C_48) | ~r2_hidden(A_46, k2_zfmisc_1(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.44/3.48  tff(c_15242, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_12')), '#skF_9')), inference(resolution, [status(thm)], [c_15142, c_36])).
% 9.44/3.48  tff(c_15268, plain, (r2_hidden(k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_926, c_15242])).
% 9.44/3.48  tff(c_15528, plain, (m1_subset_1(k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12'), '#skF_9')), inference(resolution, [status(thm)], [c_15268, c_20])).
% 9.44/3.48  tff(c_577, plain, (![B_196, A_195]: (k2_mcart_1(B_196)='#skF_6'(A_195, B_196) | ~r2_hidden(B_196, A_195) | ~v1_relat_1(A_195))), inference(superposition, [status(thm), theory('equality')], [c_564, c_64])).
% 9.44/3.48  tff(c_15225, plain, ('#skF_6'(k2_zfmisc_1('#skF_8', '#skF_9'), k1_mcart_1('#skF_12'))=k2_mcart_1(k1_mcart_1('#skF_12')) | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_15142, c_577])).
% 9.44/3.48  tff(c_15255, plain, ('#skF_6'(k2_zfmisc_1('#skF_8', '#skF_9'), k1_mcart_1('#skF_12'))=k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_926, c_15225])).
% 9.44/3.48  tff(c_292, plain, (![A_145, C_146, B_147]: (r2_hidden(k2_mcart_1(A_145), C_146) | ~r2_hidden(A_145, k2_zfmisc_1(B_147, C_146)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.44/3.48  tff(c_294, plain, (![A_145, C_41, A_39, B_40]: (r2_hidden(k2_mcart_1(A_145), C_41) | ~r2_hidden(A_145, k3_zfmisc_1(A_39, B_40, C_41)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_292])).
% 9.44/3.48  tff(c_15155, plain, (r2_hidden(k2_mcart_1('#skF_12'), '#skF_10')), inference(resolution, [status(thm)], [c_14926, c_294])).
% 9.44/3.48  tff(c_15187, plain, (m1_subset_1(k2_mcart_1('#skF_12'), '#skF_10')), inference(resolution, [status(thm)], [c_15155, c_20])).
% 9.44/3.48  tff(c_776, plain, (![A_230, B_231, C_232, D_233]: (k7_mcart_1(A_230, B_231, C_232, D_233)=k2_mcart_1(D_233) | ~m1_subset_1(D_233, k3_zfmisc_1(A_230, B_231, C_232)) | k1_xboole_0=C_232 | k1_xboole_0=B_231 | k1_xboole_0=A_230)), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.44/3.48  tff(c_798, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12')=k2_mcart_1('#skF_12') | k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_76, c_776])).
% 9.44/3.48  tff(c_807, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12')=k2_mcart_1('#skF_12')), inference(negUnitSimplification, [status(thm)], [c_72, c_70, c_68, c_798])).
% 9.44/3.48  tff(c_66, plain, (k7_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12')!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.44/3.48  tff(c_808, plain, (k2_mcart_1('#skF_12')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_807, c_66])).
% 9.44/3.48  tff(c_14925, plain, (k4_tarski(k1_mcart_1('#skF_12'), k2_mcart_1('#skF_12'))='#skF_12'), inference(splitRight, [status(thm)], [c_12852])).
% 9.44/3.48  tff(c_30, plain, (![A_36, B_37, C_38]: (k4_tarski(k4_tarski(A_36, B_37), C_38)=k3_mcart_1(A_36, B_37, C_38))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.44/3.48  tff(c_12388, plain, (![A_673, B_674, C_675]: (k3_mcart_1('#skF_5'(A_673, B_674), '#skF_6'(A_673, B_674), C_675)=k4_tarski(B_674, C_675) | ~r2_hidden(B_674, A_673) | ~v1_relat_1(A_673))), inference(superposition, [status(thm), theory('equality')], [c_564, c_30])).
% 9.44/3.48  tff(c_74, plain, (![H_91, F_85, G_89]: (H_91='#skF_11' | k3_mcart_1(F_85, G_89, H_91)!='#skF_12' | ~m1_subset_1(H_91, '#skF_10') | ~m1_subset_1(G_89, '#skF_9') | ~m1_subset_1(F_85, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.44/3.48  tff(c_12404, plain, (![C_675, B_674, A_673]: (C_675='#skF_11' | k4_tarski(B_674, C_675)!='#skF_12' | ~m1_subset_1(C_675, '#skF_10') | ~m1_subset_1('#skF_6'(A_673, B_674), '#skF_9') | ~m1_subset_1('#skF_5'(A_673, B_674), '#skF_8') | ~r2_hidden(B_674, A_673) | ~v1_relat_1(A_673))), inference(superposition, [status(thm), theory('equality')], [c_12388, c_74])).
% 9.44/3.48  tff(c_14931, plain, (![A_673]: (k2_mcart_1('#skF_12')='#skF_11' | ~m1_subset_1(k2_mcart_1('#skF_12'), '#skF_10') | ~m1_subset_1('#skF_6'(A_673, k1_mcart_1('#skF_12')), '#skF_9') | ~m1_subset_1('#skF_5'(A_673, k1_mcart_1('#skF_12')), '#skF_8') | ~r2_hidden(k1_mcart_1('#skF_12'), A_673) | ~v1_relat_1(A_673))), inference(superposition, [status(thm), theory('equality')], [c_14925, c_12404])).
% 9.44/3.48  tff(c_14954, plain, (![A_673]: (~m1_subset_1(k2_mcart_1('#skF_12'), '#skF_10') | ~m1_subset_1('#skF_6'(A_673, k1_mcart_1('#skF_12')), '#skF_9') | ~m1_subset_1('#skF_5'(A_673, k1_mcart_1('#skF_12')), '#skF_8') | ~r2_hidden(k1_mcart_1('#skF_12'), A_673) | ~v1_relat_1(A_673))), inference(negUnitSimplification, [status(thm)], [c_808, c_14931])).
% 9.44/3.48  tff(c_19886, plain, (![A_857]: (~m1_subset_1('#skF_6'(A_857, k1_mcart_1('#skF_12')), '#skF_9') | ~m1_subset_1('#skF_5'(A_857, k1_mcart_1('#skF_12')), '#skF_8') | ~r2_hidden(k1_mcart_1('#skF_12'), A_857) | ~v1_relat_1(A_857))), inference(demodulation, [status(thm), theory('equality')], [c_15187, c_14954])).
% 9.44/3.48  tff(c_19889, plain, (~m1_subset_1(k6_mcart_1('#skF_8', '#skF_9', '#skF_10', '#skF_12'), '#skF_9') | ~m1_subset_1('#skF_5'(k2_zfmisc_1('#skF_8', '#skF_9'), k1_mcart_1('#skF_12')), '#skF_8') | ~r2_hidden(k1_mcart_1('#skF_12'), k2_zfmisc_1('#skF_8', '#skF_9')) | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_15255, c_19886])).
% 9.44/3.48  tff(c_19895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_15142, c_15498, c_15258, c_15528, c_19889])).
% 9.44/3.48  tff(c_19896, plain, (v1_xboole_0('#skF_12')), inference(splitRight, [status(thm)], [c_239])).
% 9.44/3.48  tff(c_168, plain, (![A_119]: (r2_hidden('#skF_7'(A_119), A_119) | k1_xboole_0=A_119)), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.44/3.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.44/3.48  tff(c_176, plain, (![A_119]: (~v1_xboole_0(A_119) | k1_xboole_0=A_119)), inference(resolution, [status(thm)], [c_168, c_2])).
% 9.44/3.48  tff(c_19904, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_19896, c_176])).
% 9.44/3.48  tff(c_19917, plain, ('#skF_8'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_72])).
% 9.44/3.48  tff(c_19916, plain, ('#skF_9'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_70])).
% 9.44/3.48  tff(c_19914, plain, ('#skF_10'!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_68])).
% 9.44/3.48  tff(c_60, plain, (![B_73, C_74, D_75]: (k4_zfmisc_1(k1_xboole_0, B_73, C_74, D_75)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.44/3.48  tff(c_19907, plain, (![B_73, C_74, D_75]: (k4_zfmisc_1('#skF_12', B_73, C_74, D_75)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_19904, c_60])).
% 9.44/3.48  tff(c_19897, plain, (v1_xboole_0(k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_239])).
% 9.44/3.48  tff(c_19908, plain, (![A_119]: (~v1_xboole_0(A_119) | A_119='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_176])).
% 9.44/3.48  tff(c_19945, plain, (k3_zfmisc_1('#skF_8', '#skF_9', '#skF_10')='#skF_12'), inference(resolution, [status(thm)], [c_19897, c_19908])).
% 9.44/3.48  tff(c_20138, plain, (![A_893, B_894, C_895, D_896]: (k2_zfmisc_1(k3_zfmisc_1(A_893, B_894, C_895), D_896)=k4_zfmisc_1(A_893, B_894, C_895, D_896))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.44/3.48  tff(c_20190, plain, (![D_907]: (k4_zfmisc_1('#skF_8', '#skF_9', '#skF_10', D_907)=k2_zfmisc_1('#skF_12', D_907))), inference(superposition, [status(thm), theory('equality')], [c_19945, c_20138])).
% 9.44/3.48  tff(c_54, plain, (![A_72, B_73, C_74]: (k4_zfmisc_1(A_72, B_73, C_74, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.44/3.48  tff(c_19910, plain, (![A_72, B_73, C_74]: (k4_zfmisc_1(A_72, B_73, C_74, '#skF_12')='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_19904, c_54])).
% 9.44/3.48  tff(c_20199, plain, (k2_zfmisc_1('#skF_12', '#skF_12')='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_20190, c_19910])).
% 9.44/3.48  tff(c_20283, plain, (![C_915]: (k3_zfmisc_1('#skF_12', '#skF_12', C_915)=k2_zfmisc_1('#skF_12', C_915))), inference(superposition, [status(thm), theory('equality')], [c_20199, c_32])).
% 9.44/3.48  tff(c_34, plain, (![A_42, B_43, C_44, D_45]: (k2_zfmisc_1(k3_zfmisc_1(A_42, B_43, C_44), D_45)=k4_zfmisc_1(A_42, B_43, C_44, D_45))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.44/3.48  tff(c_20289, plain, (![C_915, D_45]: (k2_zfmisc_1(k2_zfmisc_1('#skF_12', C_915), D_45)=k4_zfmisc_1('#skF_12', '#skF_12', C_915, D_45))), inference(superposition, [status(thm), theory('equality')], [c_20283, c_34])).
% 9.44/3.48  tff(c_20296, plain, (![C_915, D_45]: (k3_zfmisc_1('#skF_12', C_915, D_45)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_19907, c_32, c_20289])).
% 9.44/3.48  tff(c_20217, plain, (![C_41]: (k3_zfmisc_1('#skF_12', '#skF_12', C_41)=k2_zfmisc_1('#skF_12', C_41))), inference(superposition, [status(thm), theory('equality')], [c_20199, c_32])).
% 9.44/3.48  tff(c_20299, plain, (![C_41]: (k2_zfmisc_1('#skF_12', C_41)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_20296, c_20217])).
% 9.44/3.48  tff(c_20156, plain, (![D_896]: (k4_zfmisc_1('#skF_8', '#skF_9', '#skF_10', D_896)=k2_zfmisc_1('#skF_12', D_896))), inference(superposition, [status(thm), theory('equality')], [c_19945, c_20138])).
% 9.44/3.48  tff(c_20315, plain, (![D_896]: (k4_zfmisc_1('#skF_8', '#skF_9', '#skF_10', D_896)='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_20299, c_20156])).
% 9.44/3.48  tff(c_52, plain, (![A_72, B_73, C_74, D_75]: (k4_zfmisc_1(A_72, B_73, C_74, D_75)!=k1_xboole_0 | k1_xboole_0=D_75 | k1_xboole_0=C_74 | k1_xboole_0=B_73 | k1_xboole_0=A_72)), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.44/3.48  tff(c_20586, plain, (![A_964, B_965, C_966, D_967]: (k4_zfmisc_1(A_964, B_965, C_966, D_967)!='#skF_12' | D_967='#skF_12' | C_966='#skF_12' | B_965='#skF_12' | A_964='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_19904, c_19904, c_19904, c_19904, c_52])).
% 9.44/3.48  tff(c_20589, plain, (![D_896]: (D_896='#skF_12' | '#skF_10'='#skF_12' | '#skF_9'='#skF_12' | '#skF_8'='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_20315, c_20586])).
% 9.44/3.48  tff(c_20613, plain, (![D_968]: (D_968='#skF_12')), inference(negUnitSimplification, [status(thm)], [c_19917, c_19916, c_19914, c_20589])).
% 9.44/3.48  tff(c_20113, plain, (![A_887, B_888, C_889]: (k4_tarski(k4_tarski(A_887, B_888), C_889)=k3_mcart_1(A_887, B_888, C_889))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.44/3.48  tff(c_8, plain, (![A_5, B_6]: (~v1_xboole_0(k4_tarski(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.44/3.48  tff(c_20128, plain, (![A_887, B_888, C_889]: (~v1_xboole_0(k3_mcart_1(A_887, B_888, C_889)))), inference(superposition, [status(thm), theory('equality')], [c_20113, c_8])).
% 9.44/3.48  tff(c_20656, plain, (~v1_xboole_0('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_20613, c_20128])).
% 9.44/3.48  tff(c_20719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19896, c_20656])).
% 9.44/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.44/3.48  
% 9.44/3.48  Inference rules
% 9.44/3.48  ----------------------
% 9.44/3.48  #Ref     : 2
% 9.44/3.48  #Sup     : 5412
% 9.44/3.48  #Fact    : 0
% 9.44/3.48  #Define  : 0
% 9.44/3.48  #Split   : 8
% 9.44/3.48  #Chain   : 0
% 9.44/3.48  #Close   : 0
% 9.44/3.48  
% 9.44/3.48  Ordering : KBO
% 9.44/3.48  
% 9.44/3.48  Simplification rules
% 9.44/3.48  ----------------------
% 9.44/3.48  #Subsume      : 956
% 9.44/3.48  #Demod        : 2738
% 9.44/3.48  #Tautology    : 3372
% 9.44/3.48  #SimpNegUnit  : 59
% 9.44/3.48  #BackRed      : 22
% 9.44/3.48  
% 9.44/3.48  #Partial instantiations: 0
% 9.44/3.48  #Strategies tried      : 1
% 9.44/3.48  
% 9.44/3.48  Timing (in seconds)
% 9.44/3.48  ----------------------
% 9.44/3.48  Preprocessing        : 0.36
% 9.44/3.48  Parsing              : 0.20
% 9.44/3.48  CNF conversion       : 0.03
% 9.44/3.48  Main loop            : 2.29
% 9.44/3.48  Inferencing          : 0.69
% 9.44/3.48  Reduction            : 0.73
% 9.44/3.48  Demodulation         : 0.51
% 9.44/3.48  BG Simplification    : 0.07
% 9.44/3.48  Subsumption          : 0.63
% 9.44/3.48  Abstraction          : 0.10
% 9.44/3.48  MUC search           : 0.00
% 9.44/3.48  Cooper               : 0.00
% 9.44/3.48  Total                : 2.70
% 9.44/3.48  Index Insertion      : 0.00
% 9.44/3.48  Index Deletion       : 0.00
% 9.44/3.48  Index Matching       : 0.00
% 9.44/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
