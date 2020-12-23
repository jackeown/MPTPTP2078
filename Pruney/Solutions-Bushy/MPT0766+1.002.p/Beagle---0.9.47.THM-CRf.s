%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0766+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:49 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 162 expanded)
%              Number of leaves         :   32 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 513 expanded)
%              Number of equality atoms :   14 (  45 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_wellord1 > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_8 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( v2_wellord1(A)
         => ! [B] :
              ~ ( r2_hidden(B,k3_relat_1(A))
                & ? [C] :
                    ( r2_hidden(C,k3_relat_1(A))
                    & ~ r2_hidden(k4_tarski(C,B),A) )
                & ! [C] :
                    ~ ( r2_hidden(C,k3_relat_1(A))
                      & r2_hidden(k4_tarski(B,C),A)
                      & ! [D] :
                          ~ ( r2_hidden(D,k3_relat_1(A))
                            & r2_hidden(k4_tarski(B,D),A)
                            & D != B
                            & ~ r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => ? [C] :
        ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,k3_relat_1(A))
            & ~ r2_hidden(k4_tarski(D,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e7_18__wellord1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( r2_hidden(D,B)
                       => r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1('#skF_2'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( r2_hidden(A_29,B_30)
      | v1_xboole_0(B_30)
      | ~ m1_subset_1(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_114,plain,(
    ! [C_66,B_67,A_68] :
      ( ~ v1_xboole_0(C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_119,plain,(
    ! [C_69,A_70] :
      ( ~ v1_xboole_0(C_69)
      | ~ r2_hidden(A_70,'#skF_2'(k1_zfmisc_1(C_69))) ) ),
    inference(resolution,[status(thm)],[c_12,c_114])).

tff(c_195,plain,(
    ! [C_91,A_92] :
      ( ~ v1_xboole_0(C_91)
      | v1_xboole_0('#skF_2'(k1_zfmisc_1(C_91)))
      | ~ m1_subset_1(A_92,'#skF_2'(k1_zfmisc_1(C_91))) ) ),
    inference(resolution,[status(thm)],[c_24,c_119])).

tff(c_200,plain,(
    ! [C_93] :
      ( ~ v1_xboole_0(C_93)
      | v1_xboole_0('#skF_2'(k1_zfmisc_1(C_93))) ) ),
    inference(resolution,[status(thm)],[c_12,c_195])).

tff(c_28,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_205,plain,(
    ! [C_94] :
      ( '#skF_2'(k1_zfmisc_1(C_94)) = k1_xboole_0
      | ~ v1_xboole_0(C_94) ) ),
    inference(resolution,[status(thm)],[c_200,c_28])).

tff(c_229,plain,(
    ! [C_95] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_95))
      | ~ v1_xboole_0(C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_12])).

tff(c_26,plain,(
    ! [C_33,B_32,A_31] :
      ( ~ v1_xboole_0(C_33)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_232,plain,(
    ! [A_31,C_95] :
      ( ~ r2_hidden(A_31,k1_xboole_0)
      | ~ v1_xboole_0(C_95) ) ),
    inference(resolution,[status(thm)],[c_229,c_26])).

tff(c_233,plain,(
    ! [C_95] : ~ v1_xboole_0(C_95) ),
    inference(splitLeft,[status(thm)],[c_232])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_233,c_47])).

tff(c_253,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_232])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [D_75,A_76,B_77] :
      ( r2_hidden(D_75,k3_relat_1(A_76))
      | ~ r2_hidden(D_75,'#skF_3'(A_76,B_77))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_673,plain,(
    ! [A_128,B_129,B_130] :
      ( r2_hidden('#skF_1'('#skF_3'(A_128,B_129),B_130),k3_relat_1(A_128))
      | ~ v1_relat_1(A_128)
      | r1_tarski('#skF_3'(A_128,B_129),B_130) ) ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_700,plain,(
    ! [A_128,B_129] :
      ( ~ v1_relat_1(A_128)
      | r1_tarski('#skF_3'(A_128,B_129),k3_relat_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_673,c_6])).

tff(c_36,plain,(
    v2_wellord1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_34,plain,(
    r2_hidden('#skF_6',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_402,plain,(
    ! [D_113,A_114,B_115] :
      ( r2_hidden(D_113,'#skF_3'(A_114,B_115))
      | r2_hidden(k4_tarski(D_113,B_115),A_114)
      | ~ r2_hidden(D_113,k3_relat_1(A_114))
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [C_48] :
      ( r2_hidden(k4_tarski('#skF_6','#skF_8'(C_48)),'#skF_5')
      | ~ r2_hidden(k4_tarski('#skF_6',C_48),'#skF_5')
      | ~ r2_hidden(C_48,k3_relat_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_281,plain,(
    ! [C_100] :
      ( ~ r2_hidden(k4_tarski(C_100,'#skF_8'(C_100)),'#skF_5')
      | ~ r2_hidden(k4_tarski('#skF_6',C_100),'#skF_5')
      | ~ r2_hidden(C_100,k3_relat_1('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_285,plain,
    ( ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),'#skF_5')
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_281])).

tff(c_291,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_285])).

tff(c_413,plain,
    ( r2_hidden('#skF_6','#skF_3'('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_402,c_291])).

tff(c_445,plain,(
    r2_hidden('#skF_6','#skF_3'('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_413])).

tff(c_22,plain,(
    ! [A_15,B_23] :
      ( r2_hidden('#skF_4'(A_15,B_23),B_23)
      | k1_xboole_0 = B_23
      | ~ r1_tarski(B_23,k3_relat_1(A_15))
      | ~ v2_wellord1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_549,plain,(
    ! [A_121,B_122,D_123] :
      ( r2_hidden(k4_tarski('#skF_4'(A_121,B_122),D_123),A_121)
      | ~ r2_hidden(D_123,B_122)
      | k1_xboole_0 = B_122
      | ~ r1_tarski(B_122,k3_relat_1(A_121))
      | ~ v2_wellord1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    ! [D_14,B_9,A_8] :
      ( ~ r2_hidden(k4_tarski(D_14,B_9),A_8)
      | ~ r2_hidden(D_14,'#skF_3'(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1264,plain,(
    ! [A_173,B_174,D_175] :
      ( ~ r2_hidden('#skF_4'(A_173,B_174),'#skF_3'(A_173,D_175))
      | ~ r2_hidden(D_175,B_174)
      | k1_xboole_0 = B_174
      | ~ r1_tarski(B_174,k3_relat_1(A_173))
      | ~ v2_wellord1(A_173)
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_549,c_16])).

tff(c_1978,plain,(
    ! [D_276,A_277] :
      ( ~ r2_hidden(D_276,'#skF_3'(A_277,D_276))
      | '#skF_3'(A_277,D_276) = k1_xboole_0
      | ~ r1_tarski('#skF_3'(A_277,D_276),k3_relat_1(A_277))
      | ~ v2_wellord1(A_277)
      | ~ v1_relat_1(A_277) ) ),
    inference(resolution,[status(thm)],[c_22,c_1264])).

tff(c_1995,plain,
    ( '#skF_3'('#skF_5','#skF_6') = k1_xboole_0
    | ~ r1_tarski('#skF_3'('#skF_5','#skF_6'),k3_relat_1('#skF_5'))
    | ~ v2_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_445,c_1978])).

tff(c_2014,plain,
    ( '#skF_3'('#skF_5','#skF_6') = k1_xboole_0
    | ~ r1_tarski('#skF_3'('#skF_5','#skF_6'),k3_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1995])).

tff(c_2077,plain,(
    ~ r1_tarski('#skF_3'('#skF_5','#skF_6'),k3_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2014])).

tff(c_2080,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_700,c_2077])).

tff(c_2084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2080])).

tff(c_2085,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2014])).

tff(c_2090,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_445])).

tff(c_2099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_2090])).

%------------------------------------------------------------------------------
