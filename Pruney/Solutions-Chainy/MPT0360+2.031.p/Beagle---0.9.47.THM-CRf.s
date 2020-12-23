%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:22 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 177 expanded)
%              Number of leaves         :   42 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  132 ( 270 expanded)
%              Number of equality atoms :   40 (  79 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_101,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_80,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_82,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_84,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_58,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4056,plain,(
    ! [C_322,A_323,B_324] :
      ( r1_tarski(C_322,k3_subset_1(A_323,B_324))
      | ~ r1_tarski(B_324,k3_subset_1(A_323,C_322))
      | ~ m1_subset_1(C_322,k1_zfmisc_1(A_323))
      | ~ m1_subset_1(B_324,k1_zfmisc_1(A_323)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4063,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_4056])).

tff(c_4075,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4063])).

tff(c_4303,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4075])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [A_39] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    ! [A_30] : k1_subset_1(A_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_31] : k2_subset_1(A_31) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    ! [A_32] : k3_subset_1(A_32,k1_subset_1(A_32)) = k2_subset_1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_64,plain,(
    ! [A_32] : k3_subset_1(A_32,k1_subset_1(A_32)) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_67,plain,(
    ! [A_32] : k3_subset_1(A_32,k1_xboole_0) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_64])).

tff(c_50,plain,(
    ! [A_37] :
      ( r1_tarski(k1_subset_1(A_37),k3_subset_1(A_37,k1_subset_1(A_37)))
      | ~ m1_subset_1(k1_subset_1(A_37),k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_63,plain,(
    ! [A_37] :
      ( r1_tarski(k1_subset_1(A_37),k2_subset_1(A_37))
      | ~ m1_subset_1(k1_subset_1(A_37),k1_zfmisc_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50])).

tff(c_65,plain,(
    ! [A_37] :
      ( r1_tarski(k1_subset_1(A_37),A_37)
      | ~ m1_subset_1(k1_subset_1(A_37),k1_zfmisc_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_63])).

tff(c_68,plain,(
    ! [A_37] :
      ( r1_tarski(k1_xboole_0,A_37)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_65])).

tff(c_70,plain,(
    ! [A_37] : r1_tarski(k1_xboole_0,A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_4068,plain,(
    ! [C_322,A_323] :
      ( r1_tarski(C_322,k3_subset_1(A_323,k1_xboole_0))
      | ~ m1_subset_1(C_322,k1_zfmisc_1(A_323))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_323)) ) ),
    inference(resolution,[status(thm)],[c_70,c_4056])).

tff(c_4081,plain,(
    ! [C_325,A_326] :
      ( r1_tarski(C_325,A_326)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(A_326)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_67,c_4068])).

tff(c_4139,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_4081])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4592,plain,(
    ! [A_348] :
      ( r1_tarski(A_348,'#skF_2')
      | ~ r1_tarski(A_348,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4139,c_8])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5017,plain,(
    ! [A_372] :
      ( k3_xboole_0(A_372,'#skF_2') = A_372
      | ~ r1_tarski(A_372,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4592,c_10])).

tff(c_5052,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_60,c_5017])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5056,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5052,c_6])).

tff(c_5059,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5056])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5064,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5059,c_18])).

tff(c_5067,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5064])).

tff(c_3216,plain,(
    ! [A_249,B_250] :
      ( k3_xboole_0(A_249,B_250) = A_249
      | ~ r1_tarski(A_249,B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3231,plain,(
    ! [A_37] : k3_xboole_0(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70,c_3216])).

tff(c_3305,plain,(
    ! [A_264,B_265] : k5_xboole_0(A_264,k3_xboole_0(A_264,B_265)) = k4_xboole_0(A_264,B_265) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3323,plain,(
    ! [A_37] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_3231,c_3305])).

tff(c_3338,plain,(
    ! [A_266] : k4_xboole_0(k1_xboole_0,A_266) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_3323])).

tff(c_3343,plain,(
    ! [A_266] : k5_xboole_0(A_266,k1_xboole_0) = k2_xboole_0(A_266,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3338,c_18])).

tff(c_3347,plain,(
    ! [A_266] : k2_xboole_0(A_266,k1_xboole_0) = A_266 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3343])).

tff(c_24,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    ! [A_24] : r1_tarski(A_24,k1_zfmisc_1(k3_tarski(A_24))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3298,plain,(
    ! [B_261,C_262,A_263] :
      ( r2_hidden(B_261,C_262)
      | ~ r1_tarski(k2_tarski(A_263,B_261),C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3302,plain,(
    ! [B_261,A_263] : r2_hidden(B_261,k1_zfmisc_1(k3_tarski(k2_tarski(A_263,B_261)))) ),
    inference(resolution,[status(thm)],[c_26,c_3298])).

tff(c_3362,plain,(
    ! [B_268,A_269] : r2_hidden(B_268,k1_zfmisc_1(k2_xboole_0(A_269,B_268))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3302])).

tff(c_3380,plain,(
    ! [A_273] : r2_hidden(k1_xboole_0,k1_zfmisc_1(A_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3347,c_3362])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3384,plain,(
    ! [A_273] : ~ v1_xboole_0(k1_zfmisc_1(A_273)) ),
    inference(resolution,[status(thm)],[c_3380,c_2])).

tff(c_3304,plain,(
    ! [B_261,A_263] : r2_hidden(B_261,k1_zfmisc_1(k2_xboole_0(A_263,B_261))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_3302])).

tff(c_3437,plain,(
    ! [B_279,A_280] :
      ( m1_subset_1(B_279,A_280)
      | ~ r2_hidden(B_279,A_280)
      | v1_xboole_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3452,plain,(
    ! [B_261,A_263] :
      ( m1_subset_1(B_261,k1_zfmisc_1(k2_xboole_0(A_263,B_261)))
      | v1_xboole_0(k1_zfmisc_1(k2_xboole_0(A_263,B_261))) ) ),
    inference(resolution,[status(thm)],[c_3304,c_3437])).

tff(c_3473,plain,(
    ! [B_261,A_263] : m1_subset_1(B_261,k1_zfmisc_1(k2_xboole_0(A_263,B_261))) ),
    inference(negUnitSimplification,[status(thm)],[c_3384,c_3452])).

tff(c_5096,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5067,c_3473])).

tff(c_5114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4303,c_5096])).

tff(c_5116,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4075])).

tff(c_5115,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4075])).

tff(c_6275,plain,(
    ! [A_446] :
      ( r1_tarski(A_446,k3_subset_1('#skF_2','#skF_3'))
      | ~ r1_tarski(A_446,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5115,c_8])).

tff(c_52,plain,(
    ! [A_37,B_38] :
      ( k1_subset_1(A_37) = B_38
      | ~ r1_tarski(B_38,k3_subset_1(A_37,B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_66,plain,(
    ! [B_38,A_37] :
      ( k1_xboole_0 = B_38
      | ~ r1_tarski(B_38,k3_subset_1(A_37,B_38))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_6283,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6275,c_66])).

tff(c_6303,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5116,c_6283])).

tff(c_6305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.36  
% 6.38/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.38/2.36  
% 6.38/2.36  %Foreground sorts:
% 6.38/2.36  
% 6.38/2.36  
% 6.38/2.36  %Background operators:
% 6.38/2.36  
% 6.38/2.36  
% 6.38/2.36  %Foreground operators:
% 6.38/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.38/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.38/2.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.38/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.38/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.38/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.38/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.38/2.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.38/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.38/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.38/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.38/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.38/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.38/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.38/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.38/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.38/2.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.38/2.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.38/2.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.38/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.38/2.36  
% 6.38/2.37  tff(f_110, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 6.38/2.37  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 6.38/2.37  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.38/2.37  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.38/2.37  tff(f_101, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.38/2.37  tff(f_80, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 6.38/2.37  tff(f_82, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.38/2.37  tff(f_84, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 6.38/2.37  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 6.38/2.37  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.38/2.37  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.38/2.37  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.38/2.37  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.38/2.37  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.38/2.37  tff(f_59, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 6.38/2.37  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.38/2.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.38/2.37  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.38/2.37  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.38/2.37  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.38/2.37  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.38/2.37  tff(c_58, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.38/2.37  tff(c_4056, plain, (![C_322, A_323, B_324]: (r1_tarski(C_322, k3_subset_1(A_323, B_324)) | ~r1_tarski(B_324, k3_subset_1(A_323, C_322)) | ~m1_subset_1(C_322, k1_zfmisc_1(A_323)) | ~m1_subset_1(B_324, k1_zfmisc_1(A_323)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.38/2.37  tff(c_4063, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_4056])).
% 6.38/2.37  tff(c_4075, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4063])).
% 6.38/2.37  tff(c_4303, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4075])).
% 6.38/2.37  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.38/2.37  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.38/2.37  tff(c_54, plain, (![A_39]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.38/2.37  tff(c_42, plain, (![A_30]: (k1_subset_1(A_30)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.38/2.37  tff(c_44, plain, (![A_31]: (k2_subset_1(A_31)=A_31)), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.38/2.37  tff(c_46, plain, (![A_32]: (k3_subset_1(A_32, k1_subset_1(A_32))=k2_subset_1(A_32))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.38/2.37  tff(c_64, plain, (![A_32]: (k3_subset_1(A_32, k1_subset_1(A_32))=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 6.38/2.38  tff(c_67, plain, (![A_32]: (k3_subset_1(A_32, k1_xboole_0)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_64])).
% 6.38/2.38  tff(c_50, plain, (![A_37]: (r1_tarski(k1_subset_1(A_37), k3_subset_1(A_37, k1_subset_1(A_37))) | ~m1_subset_1(k1_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.38/2.38  tff(c_63, plain, (![A_37]: (r1_tarski(k1_subset_1(A_37), k2_subset_1(A_37)) | ~m1_subset_1(k1_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50])).
% 6.38/2.38  tff(c_65, plain, (![A_37]: (r1_tarski(k1_subset_1(A_37), A_37) | ~m1_subset_1(k1_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_63])).
% 6.38/2.38  tff(c_68, plain, (![A_37]: (r1_tarski(k1_xboole_0, A_37) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_65])).
% 6.38/2.38  tff(c_70, plain, (![A_37]: (r1_tarski(k1_xboole_0, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68])).
% 6.38/2.38  tff(c_4068, plain, (![C_322, A_323]: (r1_tarski(C_322, k3_subset_1(A_323, k1_xboole_0)) | ~m1_subset_1(C_322, k1_zfmisc_1(A_323)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_323)))), inference(resolution, [status(thm)], [c_70, c_4056])).
% 6.38/2.38  tff(c_4081, plain, (![C_325, A_326]: (r1_tarski(C_325, A_326) | ~m1_subset_1(C_325, k1_zfmisc_1(A_326)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_67, c_4068])).
% 6.38/2.38  tff(c_4139, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_4081])).
% 6.38/2.38  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.38/2.38  tff(c_4592, plain, (![A_348]: (r1_tarski(A_348, '#skF_2') | ~r1_tarski(A_348, '#skF_4'))), inference(resolution, [status(thm)], [c_4139, c_8])).
% 6.38/2.38  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.38/2.38  tff(c_5017, plain, (![A_372]: (k3_xboole_0(A_372, '#skF_2')=A_372 | ~r1_tarski(A_372, '#skF_4'))), inference(resolution, [status(thm)], [c_4592, c_10])).
% 6.38/2.38  tff(c_5052, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_60, c_5017])).
% 6.38/2.38  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.38/2.38  tff(c_5056, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5052, c_6])).
% 6.38/2.38  tff(c_5059, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5056])).
% 6.38/2.38  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.38/2.38  tff(c_5064, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5059, c_18])).
% 6.38/2.38  tff(c_5067, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5064])).
% 6.38/2.38  tff(c_3216, plain, (![A_249, B_250]: (k3_xboole_0(A_249, B_250)=A_249 | ~r1_tarski(A_249, B_250))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.38/2.38  tff(c_3231, plain, (![A_37]: (k3_xboole_0(k1_xboole_0, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_3216])).
% 6.38/2.38  tff(c_3305, plain, (![A_264, B_265]: (k5_xboole_0(A_264, k3_xboole_0(A_264, B_265))=k4_xboole_0(A_264, B_265))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.38/2.38  tff(c_3323, plain, (![A_37]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_37))), inference(superposition, [status(thm), theory('equality')], [c_3231, c_3305])).
% 6.38/2.38  tff(c_3338, plain, (![A_266]: (k4_xboole_0(k1_xboole_0, A_266)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_3323])).
% 6.38/2.38  tff(c_3343, plain, (![A_266]: (k5_xboole_0(A_266, k1_xboole_0)=k2_xboole_0(A_266, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_3338, c_18])).
% 6.38/2.38  tff(c_3347, plain, (![A_266]: (k2_xboole_0(A_266, k1_xboole_0)=A_266)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_3343])).
% 6.38/2.38  tff(c_24, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.38/2.38  tff(c_26, plain, (![A_24]: (r1_tarski(A_24, k1_zfmisc_1(k3_tarski(A_24))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.38/2.38  tff(c_3298, plain, (![B_261, C_262, A_263]: (r2_hidden(B_261, C_262) | ~r1_tarski(k2_tarski(A_263, B_261), C_262))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.38/2.38  tff(c_3302, plain, (![B_261, A_263]: (r2_hidden(B_261, k1_zfmisc_1(k3_tarski(k2_tarski(A_263, B_261)))))), inference(resolution, [status(thm)], [c_26, c_3298])).
% 6.38/2.38  tff(c_3362, plain, (![B_268, A_269]: (r2_hidden(B_268, k1_zfmisc_1(k2_xboole_0(A_269, B_268))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3302])).
% 6.38/2.38  tff(c_3380, plain, (![A_273]: (r2_hidden(k1_xboole_0, k1_zfmisc_1(A_273)))), inference(superposition, [status(thm), theory('equality')], [c_3347, c_3362])).
% 6.38/2.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.38/2.38  tff(c_3384, plain, (![A_273]: (~v1_xboole_0(k1_zfmisc_1(A_273)))), inference(resolution, [status(thm)], [c_3380, c_2])).
% 6.38/2.38  tff(c_3304, plain, (![B_261, A_263]: (r2_hidden(B_261, k1_zfmisc_1(k2_xboole_0(A_263, B_261))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_3302])).
% 6.38/2.38  tff(c_3437, plain, (![B_279, A_280]: (m1_subset_1(B_279, A_280) | ~r2_hidden(B_279, A_280) | v1_xboole_0(A_280))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.38/2.38  tff(c_3452, plain, (![B_261, A_263]: (m1_subset_1(B_261, k1_zfmisc_1(k2_xboole_0(A_263, B_261))) | v1_xboole_0(k1_zfmisc_1(k2_xboole_0(A_263, B_261))))), inference(resolution, [status(thm)], [c_3304, c_3437])).
% 6.38/2.38  tff(c_3473, plain, (![B_261, A_263]: (m1_subset_1(B_261, k1_zfmisc_1(k2_xboole_0(A_263, B_261))))), inference(negUnitSimplification, [status(thm)], [c_3384, c_3452])).
% 6.38/2.38  tff(c_5096, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5067, c_3473])).
% 6.38/2.38  tff(c_5114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4303, c_5096])).
% 6.38/2.38  tff(c_5116, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4075])).
% 6.38/2.38  tff(c_5115, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_4075])).
% 6.38/2.38  tff(c_6275, plain, (![A_446]: (r1_tarski(A_446, k3_subset_1('#skF_2', '#skF_3')) | ~r1_tarski(A_446, '#skF_4'))), inference(resolution, [status(thm)], [c_5115, c_8])).
% 6.38/2.38  tff(c_52, plain, (![A_37, B_38]: (k1_subset_1(A_37)=B_38 | ~r1_tarski(B_38, k3_subset_1(A_37, B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.38/2.38  tff(c_66, plain, (![B_38, A_37]: (k1_xboole_0=B_38 | ~r1_tarski(B_38, k3_subset_1(A_37, B_38)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 6.38/2.38  tff(c_6283, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6275, c_66])).
% 6.38/2.38  tff(c_6303, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5116, c_6283])).
% 6.38/2.38  tff(c_6305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_6303])).
% 6.38/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.38/2.38  
% 6.38/2.38  Inference rules
% 6.38/2.38  ----------------------
% 6.38/2.38  #Ref     : 0
% 6.38/2.38  #Sup     : 1493
% 6.38/2.38  #Fact    : 0
% 6.38/2.38  #Define  : 0
% 6.38/2.38  #Split   : 9
% 6.38/2.38  #Chain   : 0
% 6.38/2.38  #Close   : 0
% 6.38/2.38  
% 6.38/2.38  Ordering : KBO
% 6.38/2.38  
% 6.38/2.38  Simplification rules
% 6.38/2.38  ----------------------
% 6.38/2.38  #Subsume      : 105
% 6.38/2.38  #Demod        : 594
% 6.38/2.38  #Tautology    : 817
% 6.38/2.38  #SimpNegUnit  : 36
% 6.38/2.38  #BackRed      : 0
% 6.38/2.38  
% 6.38/2.38  #Partial instantiations: 0
% 6.38/2.38  #Strategies tried      : 1
% 6.38/2.38  
% 6.38/2.38  Timing (in seconds)
% 6.38/2.38  ----------------------
% 6.38/2.38  Preprocessing        : 0.32
% 6.38/2.38  Parsing              : 0.17
% 6.38/2.38  CNF conversion       : 0.02
% 6.38/2.38  Main loop            : 1.27
% 6.38/2.38  Inferencing          : 0.45
% 6.38/2.38  Reduction            : 0.46
% 6.38/2.38  Demodulation         : 0.34
% 6.38/2.38  BG Simplification    : 0.04
% 6.38/2.38  Subsumption          : 0.20
% 6.38/2.38  Abstraction          : 0.05
% 6.38/2.38  MUC search           : 0.00
% 6.38/2.38  Cooper               : 0.00
% 6.38/2.38  Total                : 1.62
% 6.38/2.38  Index Insertion      : 0.00
% 6.38/2.38  Index Deletion       : 0.00
% 6.38/2.38  Index Matching       : 0.00
% 6.38/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
