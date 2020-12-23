%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0662+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:39 EST 2020

% Result     : Theorem 19.76s
% Output     : CNFRefutation 19.86s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 180 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  153 ( 489 expanded)
%              Number of equality atoms :   19 (  80 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_44,axiom,(
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

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_56,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k7_relat_1(B_28,A_27),B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    r2_hidden('#skF_3',k1_relat_1(k7_relat_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_286,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(k4_tarski(B_81,k1_funct_1(A_82,B_81)),A_82)
      | ~ r2_hidden(B_81,k1_relat_1(A_82))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    ! [B_26,A_25] :
      ( ~ v1_xboole_0(B_26)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_309,plain,(
    ! [A_83,B_84] :
      ( ~ v1_xboole_0(A_83)
      | ~ r2_hidden(B_84,k1_relat_1(A_83))
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_286,c_44])).

tff(c_327,plain,
    ( ~ v1_xboole_0(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_309])).

tff(c_351,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_367,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_351])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_367])).

tff(c_373,plain,(
    v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( v1_funct_1(k7_relat_1(A_16,B_17))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_372,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_xboole_0(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_452,plain,(
    ~ v1_xboole_0(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_372])).

tff(c_36,plain,(
    ! [A_18,B_19] :
      ( r2_hidden(A_18,B_19)
      | v1_xboole_0(B_19)
      | ~ m1_subset_1(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_738,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_funct_1(A_129,B_130) = C_131
      | ~ r2_hidden(k4_tarski(B_130,C_131),A_129)
      | ~ r2_hidden(B_130,k1_relat_1(A_129))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1997,plain,(
    ! [B_234,B_235,C_236] :
      ( k1_funct_1(B_234,B_235) = C_236
      | ~ r2_hidden(B_235,k1_relat_1(B_234))
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234)
      | v1_xboole_0(B_234)
      | ~ m1_subset_1(k4_tarski(B_235,C_236),B_234) ) ),
    inference(resolution,[status(thm)],[c_36,c_738])).

tff(c_2060,plain,(
    ! [C_236] :
      ( k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') = C_236
      | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
      | v1_xboole_0(k7_relat_1('#skF_5','#skF_4'))
      | ~ m1_subset_1(k4_tarski('#skF_3',C_236),k7_relat_1('#skF_5','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_52,c_1997])).

tff(c_2084,plain,(
    ! [C_236] :
      ( k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') = C_236
      | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
      | v1_xboole_0(k7_relat_1('#skF_5','#skF_4'))
      | ~ m1_subset_1(k4_tarski('#skF_3',C_236),k7_relat_1('#skF_5','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_2060])).

tff(c_2085,plain,(
    ! [C_236] :
      ( k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') = C_236
      | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
      | ~ m1_subset_1(k4_tarski('#skF_3',C_236),k7_relat_1('#skF_5','#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_2084])).

tff(c_2154,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2085])).

tff(c_2157,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_2154])).

tff(c_2161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2157])).

tff(c_2163,plain,(
    v1_funct_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2085])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_133,plain,(
    ! [A_53,C_54,B_55] :
      ( m1_subset_1(A_53,C_54)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(C_54))
      | ~ r2_hidden(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_136,plain,(
    ! [A_53,B_21,A_20] :
      ( m1_subset_1(A_53,B_21)
      | ~ r2_hidden(A_53,A_20)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_40,c_133])).

tff(c_32068,plain,(
    ! [B_966,A_967,B_968] :
      ( m1_subset_1(k4_tarski(B_966,k1_funct_1(A_967,B_966)),B_968)
      | ~ r1_tarski(A_967,B_968)
      | ~ r2_hidden(B_966,k1_relat_1(A_967))
      | ~ v1_funct_1(A_967)
      | ~ v1_relat_1(A_967) ) ),
    inference(resolution,[status(thm)],[c_286,c_136])).

tff(c_145,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(k1_relat_1(B_60),A_61) = k1_relat_1(k7_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_329,plain,(
    ! [D_87,B_88,A_89] :
      ( r2_hidden(D_87,k1_relat_1(B_88))
      | ~ r2_hidden(D_87,k1_relat_1(k7_relat_1(B_88,A_89)))
      | ~ v1_relat_1(B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_16])).

tff(c_344,plain,
    ( r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_329])).

tff(c_350,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_344])).

tff(c_308,plain,(
    ! [A_82,B_81] :
      ( ~ v1_xboole_0(A_82)
      | ~ r2_hidden(B_81,k1_relat_1(A_82))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(resolution,[status(thm)],[c_286,c_44])).

tff(c_376,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_350,c_308])).

tff(c_384,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_376])).

tff(c_2050,plain,(
    ! [C_236] :
      ( k1_funct_1('#skF_5','#skF_3') = C_236
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k4_tarski('#skF_3',C_236),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_350,c_1997])).

tff(c_2077,plain,(
    ! [C_236] :
      ( k1_funct_1('#skF_5','#skF_3') = C_236
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(k4_tarski('#skF_3',C_236),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_2050])).

tff(c_2078,plain,(
    ! [C_236] :
      ( k1_funct_1('#skF_5','#skF_3') = C_236
      | ~ m1_subset_1(k4_tarski('#skF_3',C_236),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_384,c_2077])).

tff(c_37194,plain,(
    ! [A_1188] :
      ( k1_funct_1(A_1188,'#skF_3') = k1_funct_1('#skF_5','#skF_3')
      | ~ r1_tarski(A_1188,'#skF_5')
      | ~ r2_hidden('#skF_3',k1_relat_1(A_1188))
      | ~ v1_funct_1(A_1188)
      | ~ v1_relat_1(A_1188) ) ),
    inference(resolution,[status(thm)],[c_32068,c_2078])).

tff(c_37228,plain,
    ( k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_5','#skF_4'),'#skF_5')
    | ~ v1_funct_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_37194])).

tff(c_37243,plain,
    ( k1_funct_1(k7_relat_1('#skF_5','#skF_4'),'#skF_3') = k1_funct_1('#skF_5','#skF_3')
    | ~ r1_tarski(k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_2163,c_37228])).

tff(c_37244,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_37243])).

tff(c_37247,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_37244])).

tff(c_37251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_37247])).

%------------------------------------------------------------------------------
