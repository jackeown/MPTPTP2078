%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:25 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 256 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 569 expanded)
%              Number of equality atoms :    0 (   0 expanded)
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

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_finset_1(A)
          & ! [B] :
              ( r2_hidden(B,A)
             => v1_finset_1(B) ) )
      <=> v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_finset_1(A)
        & ! [B] :
            ( r2_hidden(B,A)
           => v1_finset_1(B) ) )
     => v1_finset_1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_finset_1(A)
     => v1_finset_1(k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(c_14,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_26,plain,
    ( v1_finset_1(k3_tarski('#skF_2'))
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_31,plain,(
    v1_finset_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_53,plain,(
    ! [A_20] :
      ( ~ v1_finset_1('#skF_1'(A_20))
      | v1_finset_1(k3_tarski(A_20))
      | ~ v1_finset_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,
    ( ~ v1_finset_1('#skF_1'('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_34])).

tff(c_63,plain,(
    ~ v1_finset_1('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_59])).

tff(c_168,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_1'(A_36),A_36)
      | v1_finset_1(k3_tarski(A_36))
      | ~ v1_finset_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_139,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_finset_1(k3_tarski(A_32))
      | ~ v1_finset_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | v1_finset_1(k3_tarski(A_5))
      | ~ v1_finset_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20,plain,(
    ! [B_11] :
      ( v1_finset_1(k3_tarski('#skF_2'))
      | v1_finset_1(B_11)
      | ~ r2_hidden(B_11,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_finset_1(k1_zfmisc_1(A_4))
      | ~ v1_finset_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(A_1,k1_zfmisc_1(k3_tarski(A_1))) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_16,B_17] :
      ( v1_finset_1(A_16)
      | ~ v1_finset_1(B_17)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [A_18] :
      ( v1_finset_1(A_18)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_18))) ) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_51,plain,(
    ! [A_18] :
      ( v1_finset_1(A_18)
      | ~ v1_finset_1(k3_tarski(A_18)) ) ),
    inference(resolution,[status(thm)],[c_6,c_47])).

tff(c_68,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_51])).

tff(c_22,plain,(
    ! [B_11] :
      ( ~ v1_finset_1('#skF_3')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_11)
      | ~ r2_hidden(B_11,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_70,plain,(
    ! [B_11] :
      ( ~ v1_finset_1('#skF_3')
      | v1_finset_1(B_11)
      | ~ r2_hidden(B_11,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22])).

tff(c_71,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_24,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_3','#skF_2')
      | ~ v1_finset_1('#skF_2')
      | v1_finset_1(B_11)
      | ~ r2_hidden(B_11,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_89,plain,(
    ! [B_11] :
      ( r2_hidden('#skF_3','#skF_2')
      | v1_finset_1(B_11)
      | ~ r2_hidden(B_11,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_24])).

tff(c_90,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,k3_tarski(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_21,B_22] :
      ( v1_finset_1(A_21)
      | ~ v1_finset_1(k3_tarski(B_22))
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_77,plain,(
    ! [A_21] :
      ( v1_finset_1(A_21)
      | ~ r2_hidden(A_21,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_72])).

tff(c_99,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_77])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_99])).

tff(c_110,plain,(
    ! [B_27] :
      ( v1_finset_1(B_27)
      | ~ r2_hidden(B_27,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_114,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_117,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_114])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_63,c_117])).

tff(c_120,plain,(
    ! [B_11] :
      ( v1_finset_1(B_11)
      | ~ r2_hidden(B_11,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_147,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_139,c_120])).

tff(c_153,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_147])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_63,c_153])).

tff(c_156,plain,(
    ! [B_11] :
      ( v1_finset_1(B_11)
      | ~ r2_hidden(B_11,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_172,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_156])).

tff(c_175,plain,
    ( v1_finset_1('#skF_1'('#skF_4'))
    | v1_finset_1(k3_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_172])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_63,c_175])).

tff(c_179,plain,(
    v1_finset_1(k3_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_16,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_197,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_16])).

tff(c_198,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_178,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_182,plain,(
    ! [A_39,B_40] :
      ( v1_finset_1(A_39)
      | ~ v1_finset_1(B_40)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_191,plain,(
    ! [A_41] :
      ( v1_finset_1(A_41)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_41))) ) ),
    inference(resolution,[status(thm)],[c_2,c_182])).

tff(c_199,plain,(
    ! [A_42] :
      ( v1_finset_1(A_42)
      | ~ v1_finset_1(k3_tarski(A_42)) ) ),
    inference(resolution,[status(thm)],[c_6,c_191])).

tff(c_205,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_178,c_199])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_205])).

tff(c_212,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_213,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_18,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1(k3_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_233,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_213,c_18])).

tff(c_237,plain,(
    ! [A_45,B_46] :
      ( v1_finset_1(A_45)
      | ~ v1_finset_1(k3_tarski(B_46))
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_4,c_182])).

tff(c_248,plain,(
    ! [A_48] :
      ( v1_finset_1(A_48)
      | ~ r2_hidden(A_48,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_178,c_237])).

tff(c_251,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_233,c_248])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_251])).

tff(c_257,plain,(
    ~ v1_finset_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_260,plain,
    ( ~ v1_finset_1('#skF_3')
    | ~ v1_finset_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_28])).

tff(c_261,plain,(
    ~ v1_finset_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_256,plain,(
    v1_finset_1(k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_263,plain,(
    ! [A_51,B_52] :
      ( v1_finset_1(A_51)
      | ~ v1_finset_1(B_52)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_268,plain,(
    ! [A_53] :
      ( v1_finset_1(A_53)
      | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(A_53))) ) ),
    inference(resolution,[status(thm)],[c_2,c_263])).

tff(c_273,plain,(
    ! [A_54] :
      ( v1_finset_1(A_54)
      | ~ v1_finset_1(k3_tarski(A_54)) ) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_276,plain,(
    v1_finset_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_256,c_273])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_276])).

tff(c_281,plain,(
    ~ v1_finset_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_282,plain,(
    v1_finset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_30,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ v1_finset_1('#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_301,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | v1_finset_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_30])).

tff(c_302,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_301])).

tff(c_305,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,k3_tarski(B_60))
      | ~ r2_hidden(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_finset_1(A_7)
      | ~ v1_finset_1(B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_320,plain,(
    ! [A_62,B_63] :
      ( v1_finset_1(A_62)
      | ~ v1_finset_1(k3_tarski(B_63))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_305,c_12])).

tff(c_327,plain,(
    ! [A_64] :
      ( v1_finset_1(A_64)
      | ~ r2_hidden(A_64,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_256,c_320])).

tff(c_330,plain,(
    v1_finset_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_302,c_327])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.26  %$ r2_hidden > r1_tarski > v1_finset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.07/1.26  
% 2.07/1.26  %Foreground sorts:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Background operators:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Foreground operators:
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.26  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.07/1.26  
% 2.07/1.28  tff(f_60, negated_conjecture, ~(![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) <=> v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_finset_1)).
% 2.07/1.28  tff(f_44, axiom, (![A]: ((v1_finset_1(A) & (![B]: (r2_hidden(B, A) => v1_finset_1(B)))) => v1_finset_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_finset_1)).
% 2.07/1.28  tff(f_35, axiom, (![A]: (v1_finset_1(A) => v1_finset_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_finset_1)).
% 2.07/1.28  tff(f_27, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.07/1.28  tff(f_50, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_finset_1)).
% 2.07/1.28  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 2.07/1.28  tff(c_14, plain, (v1_finset_1(k3_tarski('#skF_2')) | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_34, plain, (~v1_finset_1(k3_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_14])).
% 2.07/1.28  tff(c_26, plain, (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_31, plain, (v1_finset_1('#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.07/1.28  tff(c_53, plain, (![A_20]: (~v1_finset_1('#skF_1'(A_20)) | v1_finset_1(k3_tarski(A_20)) | ~v1_finset_1(A_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.28  tff(c_59, plain, (~v1_finset_1('#skF_1'('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_53, c_34])).
% 2.07/1.28  tff(c_63, plain, (~v1_finset_1('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_59])).
% 2.07/1.28  tff(c_168, plain, (![A_36]: (r2_hidden('#skF_1'(A_36), A_36) | v1_finset_1(k3_tarski(A_36)) | ~v1_finset_1(A_36))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.28  tff(c_139, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_finset_1(k3_tarski(A_32)) | ~v1_finset_1(A_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.28  tff(c_10, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | v1_finset_1(k3_tarski(A_5)) | ~v1_finset_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.28  tff(c_20, plain, (![B_11]: (v1_finset_1(k3_tarski('#skF_2')) | v1_finset_1(B_11) | ~r2_hidden(B_11, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_64, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_20])).
% 2.07/1.28  tff(c_6, plain, (![A_4]: (v1_finset_1(k1_zfmisc_1(A_4)) | ~v1_finset_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.28  tff(c_2, plain, (![A_1]: (r1_tarski(A_1, k1_zfmisc_1(k3_tarski(A_1))))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.28  tff(c_38, plain, (![A_16, B_17]: (v1_finset_1(A_16) | ~v1_finset_1(B_17) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.28  tff(c_47, plain, (![A_18]: (v1_finset_1(A_18) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_18))))), inference(resolution, [status(thm)], [c_2, c_38])).
% 2.07/1.28  tff(c_51, plain, (![A_18]: (v1_finset_1(A_18) | ~v1_finset_1(k3_tarski(A_18)))), inference(resolution, [status(thm)], [c_6, c_47])).
% 2.07/1.28  tff(c_68, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_64, c_51])).
% 2.07/1.28  tff(c_22, plain, (![B_11]: (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1(B_11) | ~r2_hidden(B_11, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_70, plain, (![B_11]: (~v1_finset_1('#skF_3') | v1_finset_1(B_11) | ~r2_hidden(B_11, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_22])).
% 2.07/1.28  tff(c_71, plain, (~v1_finset_1('#skF_3')), inference(splitLeft, [status(thm)], [c_70])).
% 2.07/1.28  tff(c_24, plain, (![B_11]: (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1(B_11) | ~r2_hidden(B_11, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_89, plain, (![B_11]: (r2_hidden('#skF_3', '#skF_2') | v1_finset_1(B_11) | ~r2_hidden(B_11, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_24])).
% 2.07/1.28  tff(c_90, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_89])).
% 2.07/1.28  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, k3_tarski(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.28  tff(c_72, plain, (![A_21, B_22]: (v1_finset_1(A_21) | ~v1_finset_1(k3_tarski(B_22)) | ~r2_hidden(A_21, B_22))), inference(resolution, [status(thm)], [c_4, c_38])).
% 2.07/1.28  tff(c_77, plain, (![A_21]: (v1_finset_1(A_21) | ~r2_hidden(A_21, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_72])).
% 2.07/1.28  tff(c_99, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_77])).
% 2.07/1.28  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_99])).
% 2.07/1.28  tff(c_110, plain, (![B_27]: (v1_finset_1(B_27) | ~r2_hidden(B_27, '#skF_4'))), inference(splitRight, [status(thm)], [c_89])).
% 2.07/1.28  tff(c_114, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_110])).
% 2.07/1.28  tff(c_117, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_114])).
% 2.07/1.28  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_63, c_117])).
% 2.07/1.28  tff(c_120, plain, (![B_11]: (v1_finset_1(B_11) | ~r2_hidden(B_11, '#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 2.07/1.28  tff(c_147, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_139, c_120])).
% 2.07/1.28  tff(c_153, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_147])).
% 2.07/1.28  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_63, c_153])).
% 2.07/1.28  tff(c_156, plain, (![B_11]: (v1_finset_1(B_11) | ~r2_hidden(B_11, '#skF_4'))), inference(splitRight, [status(thm)], [c_20])).
% 2.07/1.28  tff(c_172, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_168, c_156])).
% 2.07/1.28  tff(c_175, plain, (v1_finset_1('#skF_1'('#skF_4')) | v1_finset_1(k3_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_172])).
% 2.07/1.28  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_63, c_175])).
% 2.07/1.28  tff(c_179, plain, (v1_finset_1(k3_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_14])).
% 2.07/1.28  tff(c_16, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_197, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_16])).
% 2.07/1.28  tff(c_198, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_197])).
% 2.07/1.28  tff(c_178, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_14])).
% 2.07/1.28  tff(c_182, plain, (![A_39, B_40]: (v1_finset_1(A_39) | ~v1_finset_1(B_40) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.28  tff(c_191, plain, (![A_41]: (v1_finset_1(A_41) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_41))))), inference(resolution, [status(thm)], [c_2, c_182])).
% 2.07/1.28  tff(c_199, plain, (![A_42]: (v1_finset_1(A_42) | ~v1_finset_1(k3_tarski(A_42)))), inference(resolution, [status(thm)], [c_6, c_191])).
% 2.07/1.28  tff(c_205, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_178, c_199])).
% 2.07/1.28  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_205])).
% 2.07/1.28  tff(c_212, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_197])).
% 2.07/1.28  tff(c_213, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_197])).
% 2.07/1.28  tff(c_18, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | ~v1_finset_1(k3_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_233, plain, (r2_hidden('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_213, c_18])).
% 2.07/1.28  tff(c_237, plain, (![A_45, B_46]: (v1_finset_1(A_45) | ~v1_finset_1(k3_tarski(B_46)) | ~r2_hidden(A_45, B_46))), inference(resolution, [status(thm)], [c_4, c_182])).
% 2.07/1.28  tff(c_248, plain, (![A_48]: (v1_finset_1(A_48) | ~r2_hidden(A_48, '#skF_2'))), inference(resolution, [status(thm)], [c_178, c_237])).
% 2.07/1.28  tff(c_251, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_233, c_248])).
% 2.07/1.28  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_251])).
% 2.07/1.28  tff(c_257, plain, (~v1_finset_1('#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 2.07/1.28  tff(c_28, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_260, plain, (~v1_finset_1('#skF_3') | ~v1_finset_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_257, c_28])).
% 2.07/1.28  tff(c_261, plain, (~v1_finset_1('#skF_2')), inference(splitLeft, [status(thm)], [c_260])).
% 2.07/1.28  tff(c_256, plain, (v1_finset_1(k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_26])).
% 2.07/1.28  tff(c_263, plain, (![A_51, B_52]: (v1_finset_1(A_51) | ~v1_finset_1(B_52) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.28  tff(c_268, plain, (![A_53]: (v1_finset_1(A_53) | ~v1_finset_1(k1_zfmisc_1(k3_tarski(A_53))))), inference(resolution, [status(thm)], [c_2, c_263])).
% 2.07/1.28  tff(c_273, plain, (![A_54]: (v1_finset_1(A_54) | ~v1_finset_1(k3_tarski(A_54)))), inference(resolution, [status(thm)], [c_6, c_268])).
% 2.07/1.28  tff(c_276, plain, (v1_finset_1('#skF_2')), inference(resolution, [status(thm)], [c_256, c_273])).
% 2.07/1.28  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_276])).
% 2.07/1.28  tff(c_281, plain, (~v1_finset_1('#skF_3')), inference(splitRight, [status(thm)], [c_260])).
% 2.07/1.28  tff(c_282, plain, (v1_finset_1('#skF_2')), inference(splitRight, [status(thm)], [c_260])).
% 2.07/1.28  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_2') | ~v1_finset_1('#skF_2') | v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.28  tff(c_301, plain, (r2_hidden('#skF_3', '#skF_2') | v1_finset_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_30])).
% 2.07/1.28  tff(c_302, plain, (r2_hidden('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_257, c_301])).
% 2.07/1.28  tff(c_305, plain, (![A_59, B_60]: (r1_tarski(A_59, k3_tarski(B_60)) | ~r2_hidden(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.28  tff(c_12, plain, (![A_7, B_8]: (v1_finset_1(A_7) | ~v1_finset_1(B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.28  tff(c_320, plain, (![A_62, B_63]: (v1_finset_1(A_62) | ~v1_finset_1(k3_tarski(B_63)) | ~r2_hidden(A_62, B_63))), inference(resolution, [status(thm)], [c_305, c_12])).
% 2.07/1.28  tff(c_327, plain, (![A_64]: (v1_finset_1(A_64) | ~r2_hidden(A_64, '#skF_2'))), inference(resolution, [status(thm)], [c_256, c_320])).
% 2.07/1.28  tff(c_330, plain, (v1_finset_1('#skF_3')), inference(resolution, [status(thm)], [c_302, c_327])).
% 2.07/1.28  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_330])).
% 2.07/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.28  
% 2.07/1.28  Inference rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Ref     : 0
% 2.07/1.28  #Sup     : 44
% 2.07/1.28  #Fact    : 0
% 2.07/1.28  #Define  : 0
% 2.07/1.28  #Split   : 9
% 2.07/1.28  #Chain   : 0
% 2.07/1.28  #Close   : 0
% 2.07/1.28  
% 2.07/1.28  Ordering : KBO
% 2.07/1.28  
% 2.07/1.28  Simplification rules
% 2.07/1.28  ----------------------
% 2.07/1.28  #Subsume      : 7
% 2.07/1.28  #Demod        : 35
% 2.07/1.28  #Tautology    : 19
% 2.07/1.28  #SimpNegUnit  : 11
% 2.07/1.28  #BackRed      : 0
% 2.07/1.28  
% 2.07/1.28  #Partial instantiations: 0
% 2.07/1.28  #Strategies tried      : 1
% 2.07/1.28  
% 2.07/1.28  Timing (in seconds)
% 2.07/1.28  ----------------------
% 2.07/1.28  Preprocessing        : 0.27
% 2.07/1.28  Parsing              : 0.15
% 2.07/1.28  CNF conversion       : 0.02
% 2.07/1.28  Main loop            : 0.23
% 2.07/1.28  Inferencing          : 0.10
% 2.07/1.28  Reduction            : 0.06
% 2.07/1.28  Demodulation         : 0.04
% 2.07/1.28  BG Simplification    : 0.01
% 2.07/1.28  Subsumption          : 0.04
% 2.07/1.28  Abstraction          : 0.01
% 2.07/1.28  MUC search           : 0.00
% 2.07/1.28  Cooper               : 0.00
% 2.07/1.28  Total                : 0.54
% 2.07/1.28  Index Insertion      : 0.00
% 2.07/1.28  Index Deletion       : 0.00
% 2.07/1.28  Index Matching       : 0.00
% 2.07/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
