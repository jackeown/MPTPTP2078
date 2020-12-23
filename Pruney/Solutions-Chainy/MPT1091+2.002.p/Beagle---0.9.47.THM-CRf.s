%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 239 expanded)
%              Number of leaves         :   19 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 540 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_finset_1(A)
          & ! [B] :
              ( r2_hidden(B,A)
             => v1_finset_1(B) ) )
      <=> v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(c_20,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_32,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39,plain,(
    v1_finset_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_70,plain,(
    ! [A_24] :
      ( ~ v1_finset_1('#skF_1'(A_24))
      | v1_finset_1(k3_tarski(A_24))
      | ~ v1_finset_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_42])).

tff(c_80,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_76])).

tff(c_159,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),A_35)
      | v1_finset_1(k3_tarski(A_35))
      | ~ v1_finset_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_141,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | v1_finset_1(k3_tarski(A_33))
      | ~ v1_finset_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | v1_finset_1(k3_tarski(A_8))
      | ~ v1_finset_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    ! [B_14] :
      ( ~ v1_finset_1('#skF_3')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_26,plain,(
    ! [B_14] :
      ( v1_finset_1(k3_tarski('#skF_2'))
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_81,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_12,plain,(
    ! [A_7] :
      ( v1_finset_1(k1_zfmisc_1(A_7))
      | ~ v1_finset_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(A_3,k1_zfmisc_1(k3_tarski(A_3))) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_18,B_19] :
      ( v1_finset_1(A_18)
      | ~ v1_finset_1(B_19)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ! [A_20] :
      ( v1_finset_1(A_20)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_20))) ) ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_58,plain,(
    ! [A_20] :
      ( v1_finset_1(A_20)
      | ~ v1_finset_1(k3_tarski(A_20)) ) ),
    inference(resolution,[status(thm)],[c_12,c_54])).

tff(c_85,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_81,c_58])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_85])).

tff(c_88,plain,(
    ! [B_14] :
      ( ~ v1_finset_1('#skF_3')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_91,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_3','#skF_2')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_99,plain,(
    ! [B_14] :
      ( r2_hidden('#skF_3','#skF_2')
      | v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_30])).

tff(c_100,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_10,plain,(
    ! [C_6,B_5,A_4] :
      ( r1_tarski(C_6,B_5)
      | ~ r2_hidden(C_6,A_4)
      | ~ r1_tarski(k3_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [B_30] :
      ( r1_tarski('#skF_3',B_30)
      | ~ r1_tarski(k3_tarski('#skF_2'),B_30) ) ),
    inference(resolution,[status(thm)],[c_100,c_10])).

tff(c_114,plain,(
    r1_tarski('#skF_3',k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( v1_finset_1(A_10)
      | ~ v1_finset_1(B_11)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_119,plain,
    ( v1_finset_1('#skF_3')
    | ~ v1_finset_1(k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_114,c_18])).

tff(c_123,plain,(
    v1_finset_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_119])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_123])).

tff(c_128,plain,(
    ! [B_31] :
      ( v1_finset_1(B_31)
      | ~ r2_hidden(B_31,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_132,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_128])).

tff(c_135,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_80,c_135])).

tff(c_138,plain,(
    ! [B_14] :
      ( v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_145,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_141,c_138])).

tff(c_148,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_80,c_148])).

tff(c_151,plain,(
    ! [B_14] :
      ( v1_finset_1(B_14)
      | ~ r2_hidden(B_14,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_163,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_151])).

tff(c_166,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_163])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_80,c_166])).

tff(c_170,plain,(
    v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_22,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_174,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_22])).

tff(c_175,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_169,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_179,plain,(
    ! [A_36,B_37] :
      ( v1_finset_1(A_36)
      | ~ v1_finset_1(B_37)
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_188,plain,(
    ! [A_38] :
      ( v1_finset_1(A_38)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_38))) ) ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_193,plain,(
    ! [A_39] :
      ( v1_finset_1(A_39)
      | ~ v1_finset_1(k3_tarski(A_39)) ) ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_199,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_169,c_193])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_199])).

tff(c_206,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_207,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_24,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_207,c_24])).

tff(c_255,plain,(
    ! [C_49,B_50,A_51] :
      ( r1_tarski(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(k3_tarski(A_51),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_262,plain,(
    ! [B_52] :
      ( r1_tarski('#skF_3',B_52)
      | ~ r1_tarski(k3_tarski('#skF_2'),B_52) ) ),
    inference(resolution,[status(thm)],[c_223,c_255])).

tff(c_272,plain,(
    r1_tarski('#skF_3',k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_262])).

tff(c_279,plain,
    ( v1_finset_1('#skF_3')
    | ~ v1_finset_1(k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_272,c_18])).

tff(c_283,plain,(
    v1_finset_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_279])).

tff(c_285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_283])).

tff(c_287,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_291,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_34])).

tff(c_292,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_291])).

tff(c_286,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_294,plain,(
    ! [A_55,B_56] :
      ( v1_finset_1(A_55)
      | ~ v1_finset_1(B_56)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_303,plain,(
    ! [A_57] :
      ( v1_finset_1(A_57)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_57))) ) ),
    inference(resolution,[status(thm)],[c_8,c_294])).

tff(c_308,plain,(
    ! [A_58] :
      ( v1_finset_1(A_58)
      | ~ v1_finset_1(k3_tarski(A_58)) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_311,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_286,c_308])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_311])).

tff(c_316,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_317,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_291])).

tff(c_36,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_319,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_36])).

tff(c_320,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_319])).

tff(c_367,plain,(
    ! [C_68,B_69,A_70] :
      ( r1_tarski(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(k3_tarski(A_70),B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_374,plain,(
    ! [B_71] :
      ( r1_tarski('#skF_3',B_71)
      | ~ r1_tarski(k3_tarski('#skF_2'),B_71) ) ),
    inference(resolution,[status(thm)],[c_320,c_367])).

tff(c_384,plain,(
    r1_tarski('#skF_3',k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_374])).

tff(c_389,plain,
    ( v1_finset_1('#skF_3')
    | ~ v1_finset_1(k3_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_384,c_18])).

tff(c_393,plain,(
    v1_finset_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_389])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.25  %$ r2_hidden > r1_tarski > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.10/1.25  
% 2.10/1.27  tff(f_68, negated_conjecture, ~(![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) <=> v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_finset_1)).
% 2.10/1.27  tff(f_52, axiom, (![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) => v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_finset_1)).
% 2.10/1.27  tff(f_43, axiom, (![A]: (v1_finset_1(A) => v1_finset_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_finset_1)).
% 2.10/1.27  tff(f_33, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.10/1.27  tff(f_58, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_finset_1)).
% 2.10/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.27  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.10/1.27  tff(c_20, plain, (v1_finset_1(k3_tarski('#skF_2')) | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_42, plain, (~v1_finset_1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_20])).
% 2.10/1.27  tff(c_32, plain, (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_39, plain, (v1_finset_1('#skF_4')), inference(splitLeft, [status(thm)], [c_32])).
% 2.10/1.27  tff(c_70, plain, (![A_24]: (~v1_finset_1('#skF_1'(A_24)) | v1_finset_1(k3_tarski(A_24)) | ~v1_finset_1(A_24))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.27  tff(c_76, plain, (~v1_finset_1('#skF_1'('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_42])).
% 2.10/1.27  tff(c_80, plain, (~v1_finset_1('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_76])).
% 2.10/1.27  tff(c_159, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), A_35) | v1_finset_1(k3_tarski(A_35)) | ~v1_finset_1(A_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.27  tff(c_141, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | v1_finset_1(k3_tarski(A_33)) | ~v1_finset_1(A_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.27  tff(c_16, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | v1_finset_1(k3_tarski(A_8)) | ~v1_finset_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.27  tff(c_28, plain, (![B_14]: (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_86, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 2.10/1.27  tff(c_26, plain, (![B_14]: (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_81, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.10/1.27  tff(c_12, plain, (![A_7]: (v1_finset_1(k1_zfmisc_1(A_7)) | ~v1_finset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.27  tff(c_8, plain, (![A_3]: (r1_tarski(A_3, k1_zfmisc_1(k3_tarski(A_3))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.27  tff(c_45, plain, (![A_18, B_19]: (v1_finset_1(A_18) | ~v1_finset_1(B_19) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_54, plain, (![A_20]: (v1_finset_1(A_20) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_20))))), inference(resolution, [status(thm)], [c_8, c_45])).
% 2.10/1.27  tff(c_58, plain, (![A_20]: (v1_finset_1(A_20) | ~v1_finset_1(k3_tarski(A_20)))), inference(resolution, [status(thm)], [c_12, c_54])).
% 2.10/1.27  tff(c_85, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_81, c_58])).
% 2.10/1.27  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_85])).
% 2.10/1.27  tff(c_88, plain, (![B_14]: (~v1_finset_1('#skF_3') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(splitRight, [status(thm)], [c_28])).
% 2.10/1.27  tff(c_91, plain, (~v1_finset_1('#skF_3')), inference(splitLeft, [status(thm)], [c_88])).
% 2.10/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.27  tff(c_89, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.10/1.27  tff(c_30, plain, (![B_14]: (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_99, plain, (![B_14]: (r2_hidden('#skF_3', '#skF_2') | v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_30])).
% 2.10/1.27  tff(c_100, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_99])).
% 2.10/1.27  tff(c_10, plain, (![C_6, B_5, A_4]: (r1_tarski(C_6, B_5) | ~r2_hidden(C_6, A_4) | ~r1_tarski(k3_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.27  tff(c_104, plain, (![B_30]: (r1_tarski('#skF_3', B_30) | ~r1_tarski(k3_tarski('#skF_2'), B_30))), inference(resolution, [status(thm)], [c_100, c_10])).
% 2.10/1.27  tff(c_114, plain, (r1_tarski('#skF_3', k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_104])).
% 2.10/1.27  tff(c_18, plain, (![A_10, B_11]: (v1_finset_1(A_10) | ~v1_finset_1(B_11) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_119, plain, (v1_finset_1('#skF_3') | ~v1_finset_1(k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_114, c_18])).
% 2.10/1.27  tff(c_123, plain, (v1_finset_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_119])).
% 2.10/1.27  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_123])).
% 2.10/1.27  tff(c_128, plain, (![B_31]: (v1_finset_1(B_31) | ~r2_hidden(B_31, '#skF_4'))), inference(splitRight, [status(thm)], [c_99])).
% 2.10/1.27  tff(c_132, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_128])).
% 2.10/1.27  tff(c_135, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_132])).
% 2.10/1.27  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_80, c_135])).
% 2.10/1.27  tff(c_138, plain, (![B_14]: (v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 2.10/1.27  tff(c_145, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_141, c_138])).
% 2.10/1.27  tff(c_148, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_145])).
% 2.10/1.27  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_80, c_148])).
% 2.10/1.27  tff(c_151, plain, (![B_14]: (v1_finset_1(B_14) | ~r2_hidden(B_14, '#skF_4'))), inference(splitRight, [status(thm)], [c_26])).
% 2.10/1.27  tff(c_163, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_159, c_151])).
% 2.10/1.27  tff(c_166, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_163])).
% 2.10/1.27  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_80, c_166])).
% 2.10/1.27  tff(c_170, plain, (v1_finset_1(k3_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_20])).
% 2.10/1.27  tff(c_22, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_174, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_22])).
% 2.10/1.27  tff(c_175, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_174])).
% 2.10/1.27  tff(c_169, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_20])).
% 2.10/1.27  tff(c_179, plain, (![A_36, B_37]: (v1_finset_1(A_36) | ~v1_finset_1(B_37) | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_188, plain, (![A_38]: (v1_finset_1(A_38) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_38))))), inference(resolution, [status(thm)], [c_8, c_179])).
% 2.10/1.27  tff(c_193, plain, (![A_39]: (v1_finset_1(A_39) | ~v1_finset_1(k3_tarski(A_39)))), inference(resolution, [status(thm)], [c_12, c_188])).
% 2.10/1.27  tff(c_199, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_169, c_193])).
% 2.10/1.27  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_199])).
% 2.10/1.27  tff(c_206, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_174])).
% 2.10/1.27  tff(c_207, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_174])).
% 2.10/1.27  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_223, plain, (r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_207, c_24])).
% 2.10/1.27  tff(c_255, plain, (![C_49, B_50, A_51]: (r1_tarski(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(k3_tarski(A_51), B_50))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.27  tff(c_262, plain, (![B_52]: (r1_tarski('#skF_3', B_52) | ~r1_tarski(k3_tarski('#skF_2'), B_52))), inference(resolution, [status(thm)], [c_223, c_255])).
% 2.10/1.27  tff(c_272, plain, (r1_tarski('#skF_3', k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_262])).
% 2.10/1.27  tff(c_279, plain, (v1_finset_1('#skF_3') | ~v1_finset_1(k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_272, c_18])).
% 2.10/1.27  tff(c_283, plain, (v1_finset_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_279])).
% 2.10/1.27  tff(c_285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_283])).
% 2.10/1.27  tff(c_287, plain, (~v1_finset_1('#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.10/1.27  tff(c_34, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_291, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_287, c_34])).
% 2.10/1.27  tff(c_292, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_291])).
% 2.10/1.27  tff(c_286, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_32])).
% 2.10/1.27  tff(c_294, plain, (![A_55, B_56]: (v1_finset_1(A_55) | ~v1_finset_1(B_56) | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.27  tff(c_303, plain, (![A_57]: (v1_finset_1(A_57) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_57))))), inference(resolution, [status(thm)], [c_8, c_294])).
% 2.10/1.27  tff(c_308, plain, (![A_58]: (v1_finset_1(A_58) | ~v1_finset_1(k3_tarski(A_58)))), inference(resolution, [status(thm)], [c_12, c_303])).
% 2.10/1.27  tff(c_311, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_286, c_308])).
% 2.10/1.27  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_311])).
% 2.10/1.27  tff(c_316, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_291])).
% 2.10/1.27  tff(c_317, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_291])).
% 2.10/1.27  tff(c_36, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_319, plain, (r2_hidden('#skF_3', '#skF_2') | v1_finset_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_317, c_36])).
% 2.10/1.27  tff(c_320, plain, (r2_hidden('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_287, c_319])).
% 2.10/1.27  tff(c_367, plain, (![C_68, B_69, A_70]: (r1_tarski(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(k3_tarski(A_70), B_69))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.27  tff(c_374, plain, (![B_71]: (r1_tarski('#skF_3', B_71) | ~r1_tarski(k3_tarski('#skF_2'), B_71))), inference(resolution, [status(thm)], [c_320, c_367])).
% 2.10/1.27  tff(c_384, plain, (r1_tarski('#skF_3', k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_6, c_374])).
% 2.10/1.27  tff(c_389, plain, (v1_finset_1('#skF_3') | ~v1_finset_1(k3_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_384, c_18])).
% 2.10/1.27  tff(c_393, plain, (v1_finset_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_389])).
% 2.10/1.27  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_393])).
% 2.10/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  Inference rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Ref     : 0
% 2.10/1.27  #Sup     : 54
% 2.10/1.27  #Fact    : 0
% 2.10/1.27  #Define  : 0
% 2.10/1.27  #Split   : 10
% 2.10/1.27  #Chain   : 0
% 2.10/1.27  #Close   : 0
% 2.10/1.27  
% 2.10/1.27  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 9
% 2.10/1.27  #Demod        : 38
% 2.10/1.27  #Tautology    : 27
% 2.10/1.27  #SimpNegUnit  : 12
% 2.10/1.27  #BackRed      : 0
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.27  Preprocessing        : 0.27
% 2.10/1.27  Parsing              : 0.15
% 2.10/1.27  CNF conversion       : 0.02
% 2.10/1.27  Main loop            : 0.23
% 2.10/1.27  Inferencing          : 0.09
% 2.10/1.27  Reduction            : 0.06
% 2.10/1.27  Demodulation         : 0.04
% 2.10/1.27  BG Simplification    : 0.01
% 2.10/1.27  Subsumption          : 0.05
% 2.10/1.27  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.54
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
