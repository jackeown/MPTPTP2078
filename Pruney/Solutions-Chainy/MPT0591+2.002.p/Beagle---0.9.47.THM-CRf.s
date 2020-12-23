%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:09 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 111 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
              & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_22] :
      ( r1_tarski(A_22,k2_zfmisc_1(k1_relat_1(A_22),k2_relat_1(A_22)))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_232,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( ~ r1_tarski(k2_zfmisc_1(A_65,B_66),k2_zfmisc_1(C_67,D_68))
      | r1_tarski(B_66,D_68)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_239,plain,(
    ! [B_66,A_65] :
      ( r1_tarski(B_66,k2_relat_1(k2_zfmisc_1(A_65,B_66)))
      | v1_xboole_0(A_65)
      | ~ v1_relat_1(k2_zfmisc_1(A_65,B_66)) ) ),
    inference(resolution,[status(thm)],[c_24,c_232])).

tff(c_250,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(B_69,k2_relat_1(k2_zfmisc_1(A_70,B_69)))
      | v1_xboole_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_239])).

tff(c_22,plain,(
    ! [A_20,B_21] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_20,B_21)),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_131,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [A_20,B_21] :
      ( k2_relat_1(k2_zfmisc_1(A_20,B_21)) = B_21
      | ~ r1_tarski(B_21,k2_relat_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_260,plain,(
    ! [A_71,B_72] :
      ( k2_relat_1(k2_zfmisc_1(A_71,B_72)) = B_72
      | v1_xboole_0(A_71) ) ),
    inference(resolution,[status(thm)],[c_250,c_139])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_18,B_19)),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_67,plain,(
    ! [B_40,A_41,D_42,C_43] :
      ( ~ r1_tarski(k2_zfmisc_1(B_40,A_41),k2_zfmisc_1(D_42,C_43))
      | r1_tarski(B_40,D_42)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_71,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(B_40,k1_relat_1(k2_zfmisc_1(B_40,A_41)))
      | v1_xboole_0(A_41)
      | ~ v1_relat_1(k2_zfmisc_1(B_40,A_41)) ) ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_81,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(B_44,k1_relat_1(k2_zfmisc_1(B_44,A_45)))
      | v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_71])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_83,plain,(
    ! [B_44,A_45] :
      ( k1_relat_1(k2_zfmisc_1(B_44,A_45)) = B_44
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(B_44,A_45)),B_44)
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_87,plain,(
    ! [B_46,A_47] :
      ( k1_relat_1(k2_zfmisc_1(B_46,A_47)) = B_46
      | v1_xboole_0(A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_26,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_4'
    | k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_47,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_111,plain,(
    v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_47])).

tff(c_36,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_2'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_111,c_40])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_115])).

tff(c_120,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_297,plain,(
    v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_120])).

tff(c_318,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_297,c_40])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 1.91/1.22  
% 1.91/1.22  %Foreground sorts:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Background operators:
% 1.91/1.22  
% 1.91/1.22  
% 1.91/1.22  %Foreground operators:
% 1.91/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.91/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.22  
% 2.06/1.23  tff(f_78, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.06/1.23  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.06/1.23  tff(f_65, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.06/1.23  tff(f_55, axiom, (![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.06/1.23  tff(f_61, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 2.06/1.23  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.23  tff(f_59, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 2.06/1.23  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.23  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.23  tff(c_18, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.06/1.23  tff(c_24, plain, (![A_22]: (r1_tarski(A_22, k2_zfmisc_1(k1_relat_1(A_22), k2_relat_1(A_22))) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.06/1.23  tff(c_232, plain, (![A_65, B_66, C_67, D_68]: (~r1_tarski(k2_zfmisc_1(A_65, B_66), k2_zfmisc_1(C_67, D_68)) | r1_tarski(B_66, D_68) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.23  tff(c_239, plain, (![B_66, A_65]: (r1_tarski(B_66, k2_relat_1(k2_zfmisc_1(A_65, B_66))) | v1_xboole_0(A_65) | ~v1_relat_1(k2_zfmisc_1(A_65, B_66)))), inference(resolution, [status(thm)], [c_24, c_232])).
% 2.06/1.23  tff(c_250, plain, (![B_69, A_70]: (r1_tarski(B_69, k2_relat_1(k2_zfmisc_1(A_70, B_69))) | v1_xboole_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_239])).
% 2.06/1.23  tff(c_22, plain, (![A_20, B_21]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_20, B_21)), B_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.23  tff(c_131, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.23  tff(c_139, plain, (![A_20, B_21]: (k2_relat_1(k2_zfmisc_1(A_20, B_21))=B_21 | ~r1_tarski(B_21, k2_relat_1(k2_zfmisc_1(A_20, B_21))))), inference(resolution, [status(thm)], [c_22, c_131])).
% 2.06/1.23  tff(c_260, plain, (![A_71, B_72]: (k2_relat_1(k2_zfmisc_1(A_71, B_72))=B_72 | v1_xboole_0(A_71))), inference(resolution, [status(thm)], [c_250, c_139])).
% 2.06/1.23  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.23  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_18, B_19)), A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.23  tff(c_67, plain, (![B_40, A_41, D_42, C_43]: (~r1_tarski(k2_zfmisc_1(B_40, A_41), k2_zfmisc_1(D_42, C_43)) | r1_tarski(B_40, D_42) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.23  tff(c_71, plain, (![B_40, A_41]: (r1_tarski(B_40, k1_relat_1(k2_zfmisc_1(B_40, A_41))) | v1_xboole_0(A_41) | ~v1_relat_1(k2_zfmisc_1(B_40, A_41)))), inference(resolution, [status(thm)], [c_24, c_67])).
% 2.06/1.23  tff(c_81, plain, (![B_44, A_45]: (r1_tarski(B_44, k1_relat_1(k2_zfmisc_1(B_44, A_45))) | v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_71])).
% 2.06/1.23  tff(c_8, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.06/1.23  tff(c_83, plain, (![B_44, A_45]: (k1_relat_1(k2_zfmisc_1(B_44, A_45))=B_44 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(B_44, A_45)), B_44) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_81, c_8])).
% 2.06/1.23  tff(c_87, plain, (![B_46, A_47]: (k1_relat_1(k2_zfmisc_1(B_46, A_47))=B_46 | v1_xboole_0(A_47))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_83])).
% 2.06/1.23  tff(c_26, plain, (k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_4' | k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.23  tff(c_47, plain, (k1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_26])).
% 2.06/1.23  tff(c_111, plain, (v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_87, c_47])).
% 2.06/1.23  tff(c_36, plain, (![A_30]: (r2_hidden('#skF_2'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.23  tff(c_40, plain, (![A_30]: (~v1_xboole_0(A_30) | k1_xboole_0=A_30)), inference(resolution, [status(thm)], [c_36, c_2])).
% 2.06/1.23  tff(c_115, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_111, c_40])).
% 2.06/1.23  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_115])).
% 2.06/1.23  tff(c_120, plain, (k2_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))!='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 2.06/1.23  tff(c_297, plain, (v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_260, c_120])).
% 2.06/1.23  tff(c_318, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_297, c_40])).
% 2.06/1.23  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_318])).
% 2.06/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 58
% 2.06/1.23  #Fact    : 0
% 2.06/1.23  #Define  : 0
% 2.06/1.23  #Split   : 2
% 2.06/1.23  #Chain   : 0
% 2.06/1.23  #Close   : 0
% 2.06/1.23  
% 2.06/1.23  Ordering : KBO
% 2.06/1.23  
% 2.06/1.23  Simplification rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Subsume      : 4
% 2.06/1.23  #Demod        : 35
% 2.06/1.23  #Tautology    : 28
% 2.06/1.23  #SimpNegUnit  : 2
% 2.06/1.23  #BackRed      : 0
% 2.06/1.23  
% 2.06/1.23  #Partial instantiations: 0
% 2.06/1.23  #Strategies tried      : 1
% 2.06/1.23  
% 2.06/1.23  Timing (in seconds)
% 2.06/1.23  ----------------------
% 2.06/1.24  Preprocessing        : 0.28
% 2.06/1.24  Parsing              : 0.15
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.19
% 2.06/1.24  Inferencing          : 0.07
% 2.06/1.24  Reduction            : 0.06
% 2.06/1.24  Demodulation         : 0.04
% 2.06/1.24  BG Simplification    : 0.01
% 2.06/1.24  Subsumption          : 0.03
% 2.06/1.24  Abstraction          : 0.01
% 2.06/1.24  MUC search           : 0.00
% 2.06/1.24  Cooper               : 0.00
% 2.06/1.24  Total                : 0.50
% 2.06/1.24  Index Insertion      : 0.00
% 2.06/1.24  Index Deletion       : 0.00
% 2.06/1.24  Index Matching       : 0.00
% 2.06/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
