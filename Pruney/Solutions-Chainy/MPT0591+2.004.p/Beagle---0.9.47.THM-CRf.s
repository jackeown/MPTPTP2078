%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:09 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 ( 110 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
              & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k2_zfmisc_1(k1_relat_1(A_18),k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_239,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( ~ r1_tarski(k2_zfmisc_1(A_59,B_60),k2_zfmisc_1(C_61,D_62))
      | r1_tarski(B_60,D_62)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_246,plain,(
    ! [B_60,A_59] :
      ( r1_tarski(B_60,k2_relat_1(k2_zfmisc_1(A_59,B_60)))
      | v1_xboole_0(A_59)
      | ~ v1_relat_1(k2_zfmisc_1(A_59,B_60)) ) ),
    inference(resolution,[status(thm)],[c_22,c_239])).

tff(c_257,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(B_63,k2_relat_1(k2_zfmisc_1(A_64,B_63)))
      | v1_xboole_0(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_246])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_16,B_17)),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_16,B_17] :
      ( k2_relat_1(k2_zfmisc_1(A_16,B_17)) = B_17
      | ~ r1_tarski(B_17,k2_relat_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_267,plain,(
    ! [A_65,B_66] :
      ( k2_relat_1(k2_zfmisc_1(A_65,B_66)) = B_66
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_257,c_146])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_64,plain,(
    ! [B_36,A_37,D_38,C_39] :
      ( ~ r1_tarski(k2_zfmisc_1(B_36,A_37),k2_zfmisc_1(D_38,C_39))
      | r1_tarski(B_36,D_38)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,(
    ! [B_36,A_37] :
      ( r1_tarski(B_36,k1_relat_1(k2_zfmisc_1(B_36,A_37)))
      | v1_xboole_0(A_37)
      | ~ v1_relat_1(k2_zfmisc_1(B_36,A_37)) ) ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_78,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(B_40,k1_relat_1(k2_zfmisc_1(B_40,A_41)))
      | v1_xboole_0(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_68])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_14,B_15)),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_45,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_14,B_15] :
      ( k1_relat_1(k2_zfmisc_1(A_14,B_15)) = A_14
      | ~ r1_tarski(A_14,k1_relat_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(resolution,[status(thm)],[c_18,c_45])).

tff(c_88,plain,(
    ! [B_42,A_43] :
      ( k1_relat_1(k2_zfmisc_1(B_42,A_43)) = B_42
      | v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_78,c_52])).

tff(c_24,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_2'
    | k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_116,plain,(
    v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_44])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    ! [B_26,A_27] :
      ( ~ v1_xboole_0(B_26)
      | B_26 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_2,c_34])).

tff(c_121,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_116,c_37])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_121])).

tff(c_128,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_304,plain,(
    v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_128])).

tff(c_325,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_304,c_37])).

tff(c_331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.25  
% 2.08/1.26  tff(f_73, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 2.08/1.26  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.08/1.26  tff(f_60, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.08/1.26  tff(f_50, axiom, (![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.08/1.26  tff(f_56, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 2.08/1.26  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.08/1.26  tff(f_54, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 2.08/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.08/1.26  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.08/1.26  tff(c_28, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.08/1.26  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.26  tff(c_22, plain, (![A_18]: (r1_tarski(A_18, k2_zfmisc_1(k1_relat_1(A_18), k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.26  tff(c_239, plain, (![A_59, B_60, C_61, D_62]: (~r1_tarski(k2_zfmisc_1(A_59, B_60), k2_zfmisc_1(C_61, D_62)) | r1_tarski(B_60, D_62) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.26  tff(c_246, plain, (![B_60, A_59]: (r1_tarski(B_60, k2_relat_1(k2_zfmisc_1(A_59, B_60))) | v1_xboole_0(A_59) | ~v1_relat_1(k2_zfmisc_1(A_59, B_60)))), inference(resolution, [status(thm)], [c_22, c_239])).
% 2.08/1.26  tff(c_257, plain, (![B_63, A_64]: (r1_tarski(B_63, k2_relat_1(k2_zfmisc_1(A_64, B_63))) | v1_xboole_0(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_246])).
% 2.08/1.26  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_16, B_17)), B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.26  tff(c_138, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.26  tff(c_146, plain, (![A_16, B_17]: (k2_relat_1(k2_zfmisc_1(A_16, B_17))=B_17 | ~r1_tarski(B_17, k2_relat_1(k2_zfmisc_1(A_16, B_17))))), inference(resolution, [status(thm)], [c_20, c_138])).
% 2.08/1.26  tff(c_267, plain, (![A_65, B_66]: (k2_relat_1(k2_zfmisc_1(A_65, B_66))=B_66 | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_257, c_146])).
% 2.08/1.26  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.08/1.26  tff(c_64, plain, (![B_36, A_37, D_38, C_39]: (~r1_tarski(k2_zfmisc_1(B_36, A_37), k2_zfmisc_1(D_38, C_39)) | r1_tarski(B_36, D_38) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.26  tff(c_68, plain, (![B_36, A_37]: (r1_tarski(B_36, k1_relat_1(k2_zfmisc_1(B_36, A_37))) | v1_xboole_0(A_37) | ~v1_relat_1(k2_zfmisc_1(B_36, A_37)))), inference(resolution, [status(thm)], [c_22, c_64])).
% 2.08/1.26  tff(c_78, plain, (![B_40, A_41]: (r1_tarski(B_40, k1_relat_1(k2_zfmisc_1(B_40, A_41))) | v1_xboole_0(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_68])).
% 2.08/1.26  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_14, B_15)), A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.26  tff(c_45, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.08/1.26  tff(c_52, plain, (![A_14, B_15]: (k1_relat_1(k2_zfmisc_1(A_14, B_15))=A_14 | ~r1_tarski(A_14, k1_relat_1(k2_zfmisc_1(A_14, B_15))))), inference(resolution, [status(thm)], [c_18, c_45])).
% 2.08/1.26  tff(c_88, plain, (![B_42, A_43]: (k1_relat_1(k2_zfmisc_1(B_42, A_43))=B_42 | v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_78, c_52])).
% 2.08/1.26  tff(c_24, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_2' | k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.08/1.26  tff(c_44, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_24])).
% 2.08/1.26  tff(c_116, plain, (v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_44])).
% 2.08/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.08/1.26  tff(c_34, plain, (![B_26, A_27]: (~v1_xboole_0(B_26) | B_26=A_27 | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.08/1.26  tff(c_37, plain, (![A_27]: (k1_xboole_0=A_27 | ~v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_2, c_34])).
% 2.08/1.26  tff(c_121, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_116, c_37])).
% 2.08/1.26  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_121])).
% 2.08/1.26  tff(c_128, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.08/1.26  tff(c_304, plain, (v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_267, c_128])).
% 2.08/1.26  tff(c_325, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_304, c_37])).
% 2.08/1.26  tff(c_331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_325])).
% 2.08/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  
% 2.08/1.26  Inference rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Ref     : 0
% 2.08/1.26  #Sup     : 62
% 2.08/1.26  #Fact    : 0
% 2.08/1.26  #Define  : 0
% 2.08/1.26  #Split   : 2
% 2.08/1.26  #Chain   : 0
% 2.08/1.26  #Close   : 0
% 2.08/1.26  
% 2.08/1.26  Ordering : KBO
% 2.08/1.26  
% 2.08/1.26  Simplification rules
% 2.08/1.26  ----------------------
% 2.08/1.26  #Subsume      : 5
% 2.08/1.26  #Demod        : 36
% 2.08/1.26  #Tautology    : 28
% 2.08/1.26  #SimpNegUnit  : 2
% 2.08/1.26  #BackRed      : 0
% 2.08/1.26  
% 2.08/1.26  #Partial instantiations: 0
% 2.08/1.26  #Strategies tried      : 1
% 2.08/1.26  
% 2.08/1.26  Timing (in seconds)
% 2.08/1.26  ----------------------
% 2.08/1.27  Preprocessing        : 0.29
% 2.08/1.27  Parsing              : 0.15
% 2.08/1.27  CNF conversion       : 0.02
% 2.08/1.27  Main loop            : 0.21
% 2.08/1.27  Inferencing          : 0.08
% 2.08/1.27  Reduction            : 0.06
% 2.08/1.27  Demodulation         : 0.05
% 2.08/1.27  BG Simplification    : 0.01
% 2.08/1.27  Subsumption          : 0.03
% 2.08/1.27  Abstraction          : 0.01
% 2.08/1.27  MUC search           : 0.00
% 2.08/1.27  Cooper               : 0.00
% 2.08/1.27  Total                : 0.53
% 2.08/1.27  Index Insertion      : 0.00
% 2.08/1.27  Index Deletion       : 0.00
% 2.08/1.27  Index Matching       : 0.00
% 2.08/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
