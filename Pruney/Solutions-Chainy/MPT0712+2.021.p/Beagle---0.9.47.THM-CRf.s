%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:34 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   49 (  62 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 104 expanded)
%              Number of equality atoms :   23 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_14,plain,(
    ! [B_5] : r1_tarski(k1_xboole_0,k1_tarski(B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(k1_tarski(A_6),B_7)
      | r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_28,B_29] :
      ( k7_relat_1(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(B_29,k1_relat_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_100,plain,(
    ! [A_28,A_6] :
      ( k7_relat_1(A_28,k1_tarski(A_6)) = k1_xboole_0
      | ~ v1_relat_1(A_28)
      | r2_hidden(A_6,k1_relat_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_16,c_92])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [C_30,A_31,B_32] :
      ( k2_tarski(k1_funct_1(C_30,A_31),k1_funct_1(C_30,B_32)) = k9_relat_1(C_30,k2_tarski(A_31,B_32))
      | ~ r2_hidden(B_32,k1_relat_1(C_30))
      | ~ r2_hidden(A_31,k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_108,plain,(
    ! [C_30,B_32] :
      ( k9_relat_1(C_30,k2_tarski(B_32,B_32)) = k1_tarski(k1_funct_1(C_30,B_32))
      | ~ r2_hidden(B_32,k1_relat_1(C_30))
      | ~ r2_hidden(B_32,k1_relat_1(C_30))
      | ~ v1_funct_1(C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_125,plain,(
    ! [C_35,B_36] :
      ( k9_relat_1(C_35,k1_tarski(B_36)) = k1_tarski(k1_funct_1(C_35,B_36))
      | ~ r2_hidden(B_36,k1_relat_1(C_35))
      | ~ r2_hidden(B_36,k1_relat_1(C_35))
      | ~ v1_funct_1(C_35)
      | ~ v1_relat_1(C_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_132,plain,(
    ! [A_37,A_38] :
      ( k9_relat_1(A_37,k1_tarski(A_38)) = k1_tarski(k1_funct_1(A_37,A_38))
      | ~ r2_hidden(A_38,k1_relat_1(A_37))
      | ~ v1_funct_1(A_37)
      | k7_relat_1(A_37,k1_tarski(A_38)) = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_100,c_125])).

tff(c_140,plain,(
    ! [A_39,A_40] :
      ( k9_relat_1(A_39,k1_tarski(A_40)) = k1_tarski(k1_funct_1(A_39,A_40))
      | ~ v1_funct_1(A_39)
      | k7_relat_1(A_39,k1_tarski(A_40)) = k1_xboole_0
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_100,c_132])).

tff(c_66,plain,(
    ! [B_24,A_25] :
      ( k2_relat_1(k7_relat_1(B_24,A_25)) = k9_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_28,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_72,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_28])).

tff(c_78,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_72])).

tff(c_146,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_78])).

tff(c_152,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_6,c_146])).

tff(c_154,plain,(
    ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_28])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n009.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:07:11 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.34  
% 2.25/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.25/1.34  
% 2.25/1.34  %Foreground sorts:
% 2.25/1.34  
% 2.25/1.34  
% 2.25/1.34  %Background operators:
% 2.25/1.34  
% 2.25/1.34  
% 2.25/1.34  %Foreground operators:
% 2.25/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.25/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.25/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.25/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.35  
% 2.25/1.36  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 2.25/1.36  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.25/1.36  tff(f_75, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_funct_1)).
% 2.25/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.25/1.36  tff(f_44, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_zfmisc_1)).
% 2.25/1.36  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.25/1.36  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.25/1.36  tff(f_68, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 2.25/1.36  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.25/1.36  tff(c_14, plain, (![B_5]: (r1_tarski(k1_xboole_0, k1_tarski(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.25/1.36  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.36  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.25/1.36  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.25/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.36  tff(c_16, plain, (![A_6, B_7]: (r1_xboole_0(k1_tarski(A_6), B_7) | r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.36  tff(c_92, plain, (![A_28, B_29]: (k7_relat_1(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(B_29, k1_relat_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.36  tff(c_100, plain, (![A_28, A_6]: (k7_relat_1(A_28, k1_tarski(A_6))=k1_xboole_0 | ~v1_relat_1(A_28) | r2_hidden(A_6, k1_relat_1(A_28)))), inference(resolution, [status(thm)], [c_16, c_92])).
% 2.25/1.36  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.36  tff(c_101, plain, (![C_30, A_31, B_32]: (k2_tarski(k1_funct_1(C_30, A_31), k1_funct_1(C_30, B_32))=k9_relat_1(C_30, k2_tarski(A_31, B_32)) | ~r2_hidden(B_32, k1_relat_1(C_30)) | ~r2_hidden(A_31, k1_relat_1(C_30)) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.25/1.36  tff(c_108, plain, (![C_30, B_32]: (k9_relat_1(C_30, k2_tarski(B_32, B_32))=k1_tarski(k1_funct_1(C_30, B_32)) | ~r2_hidden(B_32, k1_relat_1(C_30)) | ~r2_hidden(B_32, k1_relat_1(C_30)) | ~v1_funct_1(C_30) | ~v1_relat_1(C_30))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 2.25/1.36  tff(c_125, plain, (![C_35, B_36]: (k9_relat_1(C_35, k1_tarski(B_36))=k1_tarski(k1_funct_1(C_35, B_36)) | ~r2_hidden(B_36, k1_relat_1(C_35)) | ~r2_hidden(B_36, k1_relat_1(C_35)) | ~v1_funct_1(C_35) | ~v1_relat_1(C_35))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_108])).
% 2.25/1.36  tff(c_132, plain, (![A_37, A_38]: (k9_relat_1(A_37, k1_tarski(A_38))=k1_tarski(k1_funct_1(A_37, A_38)) | ~r2_hidden(A_38, k1_relat_1(A_37)) | ~v1_funct_1(A_37) | k7_relat_1(A_37, k1_tarski(A_38))=k1_xboole_0 | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_100, c_125])).
% 2.25/1.36  tff(c_140, plain, (![A_39, A_40]: (k9_relat_1(A_39, k1_tarski(A_40))=k1_tarski(k1_funct_1(A_39, A_40)) | ~v1_funct_1(A_39) | k7_relat_1(A_39, k1_tarski(A_40))=k1_xboole_0 | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_100, c_132])).
% 2.25/1.36  tff(c_66, plain, (![B_24, A_25]: (k2_relat_1(k7_relat_1(B_24, A_25))=k9_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.25/1.36  tff(c_28, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.25/1.36  tff(c_72, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_66, c_28])).
% 2.25/1.36  tff(c_78, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_72])).
% 2.25/1.36  tff(c_146, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_140, c_78])).
% 2.25/1.36  tff(c_152, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_6, c_146])).
% 2.25/1.36  tff(c_154, plain, (~r1_tarski(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_28])).
% 2.25/1.36  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_22, c_154])).
% 2.25/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.36  
% 2.25/1.36  Inference rules
% 2.25/1.36  ----------------------
% 2.25/1.36  #Ref     : 0
% 2.25/1.36  #Sup     : 27
% 2.25/1.36  #Fact    : 0
% 2.25/1.36  #Define  : 0
% 2.25/1.36  #Split   : 1
% 2.25/1.36  #Chain   : 0
% 2.25/1.36  #Close   : 0
% 2.25/1.36  
% 2.25/1.36  Ordering : KBO
% 2.25/1.36  
% 2.25/1.36  Simplification rules
% 2.25/1.36  ----------------------
% 2.25/1.36  #Subsume      : 5
% 2.25/1.36  #Demod        : 13
% 2.25/1.36  #Tautology    : 17
% 2.25/1.36  #SimpNegUnit  : 0
% 2.25/1.36  #BackRed      : 1
% 2.25/1.36  
% 2.25/1.36  #Partial instantiations: 0
% 2.25/1.36  #Strategies tried      : 1
% 2.25/1.36  
% 2.25/1.36  Timing (in seconds)
% 2.25/1.36  ----------------------
% 2.25/1.36  Preprocessing        : 0.36
% 2.25/1.36  Parsing              : 0.20
% 2.25/1.36  CNF conversion       : 0.02
% 2.25/1.36  Main loop            : 0.18
% 2.25/1.36  Inferencing          : 0.07
% 2.25/1.36  Reduction            : 0.05
% 2.25/1.36  Demodulation         : 0.04
% 2.25/1.36  BG Simplification    : 0.01
% 2.25/1.36  Subsumption          : 0.03
% 2.25/1.36  Abstraction          : 0.01
% 2.25/1.36  MUC search           : 0.00
% 2.25/1.36  Cooper               : 0.00
% 2.25/1.36  Total                : 0.57
% 2.25/1.36  Index Insertion      : 0.00
% 2.25/1.36  Index Deletion       : 0.00
% 2.25/1.36  Index Matching       : 0.00
% 2.25/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
