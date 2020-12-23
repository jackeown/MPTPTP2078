%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:22 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 130 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( v1_relat_1(D)
     => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
      <=> ( r2_hidden(A,C)
          & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

tff(c_58,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_62,plain,(
    ! [D_27,A_28,B_29] :
      ( r2_hidden(D_27,A_28)
      | ~ r2_hidden(D_27,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_62])).

tff(c_68,plain,(
    ! [D_32,B_33,A_34] :
      ( r2_hidden(D_32,B_33)
      | ~ r2_hidden(D_32,k3_xboole_0(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_68])).

tff(c_46,plain,(
    ! [A_22,C_24] :
      ( r2_hidden(k4_tarski(A_22,k1_funct_1(C_24,A_22)),C_24)
      | ~ r2_hidden(A_22,k1_relat_1(C_24))
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,(
    ! [A_21] : v1_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( v1_funct_1(k5_relat_1(A_19,B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_223,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( r2_hidden(k4_tarski(A_71,B_72),k5_relat_1(k6_relat_1(C_73),D_74))
      | ~ r2_hidden(k4_tarski(A_71,B_72),D_74)
      | ~ r2_hidden(A_71,C_73)
      | ~ v1_relat_1(D_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_48,plain,(
    ! [C_24,A_22,B_23] :
      ( k1_funct_1(C_24,A_22) = B_23
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3338,plain,(
    ! [C_285,D_286,A_287,B_288] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_285),D_286),A_287) = B_288
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_285),D_286))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(C_285),D_286))
      | ~ r2_hidden(k4_tarski(A_287,B_288),D_286)
      | ~ r2_hidden(A_287,C_285)
      | ~ v1_relat_1(D_286) ) ),
    inference(resolution,[status(thm)],[c_223,c_48])).

tff(c_3341,plain,(
    ! [C_285,B_8,A_287,B_288] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_285),B_8),A_287) = B_288
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_285),B_8))
      | ~ r2_hidden(k4_tarski(A_287,B_288),B_8)
      | ~ r2_hidden(A_287,C_285)
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(k6_relat_1(C_285)) ) ),
    inference(resolution,[status(thm)],[c_20,c_3338])).

tff(c_3345,plain,(
    ! [C_289,B_290,A_291,B_292] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_289),B_290),A_291) = B_292
      | ~ v1_funct_1(k5_relat_1(k6_relat_1(C_289),B_290))
      | ~ r2_hidden(k4_tarski(A_291,B_292),B_290)
      | ~ r2_hidden(A_291,C_289)
      | ~ v1_relat_1(B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3341])).

tff(c_3348,plain,(
    ! [C_289,B_20,A_291,B_292] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_289),B_20),A_291) = B_292
      | ~ r2_hidden(k4_tarski(A_291,B_292),B_20)
      | ~ r2_hidden(A_291,C_289)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(k6_relat_1(C_289))
      | ~ v1_relat_1(k6_relat_1(C_289)) ) ),
    inference(resolution,[status(thm)],[c_38,c_3345])).

tff(c_3352,plain,(
    ! [C_293,B_294,A_295,B_296] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_293),B_294),A_295) = B_296
      | ~ r2_hidden(k4_tarski(A_295,B_296),B_294)
      | ~ r2_hidden(A_295,C_293)
      | ~ v1_funct_1(B_294)
      | ~ v1_relat_1(B_294) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_3348])).

tff(c_3377,plain,(
    ! [C_297,C_298,A_299] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(C_297),C_298),A_299) = k1_funct_1(C_298,A_299)
      | ~ r2_hidden(A_299,C_297)
      | ~ r2_hidden(A_299,k1_relat_1(C_298))
      | ~ v1_funct_1(C_298)
      | ~ v1_relat_1(C_298) ) ),
    inference(resolution,[status(thm)],[c_46,c_3352])).

tff(c_52,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3393,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3377,c_52])).

tff(c_3408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_66,c_72,c_3393])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:08:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.94/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.17  
% 5.94/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.17  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 5.94/2.17  
% 5.94/2.17  %Foreground sorts:
% 5.94/2.17  
% 5.94/2.17  
% 5.94/2.17  %Background operators:
% 5.94/2.17  
% 5.94/2.17  
% 5.94/2.17  %Foreground operators:
% 5.94/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.94/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.94/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.94/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.94/2.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.94/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.94/2.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.94/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.94/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.94/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.94/2.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.94/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.94/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.94/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.94/2.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.94/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.94/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.94/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.94/2.17  
% 5.94/2.18  tff(f_103, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_1)).
% 5.94/2.18  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.94/2.18  tff(f_94, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 5.94/2.18  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.94/2.18  tff(f_80, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 5.94/2.18  tff(f_40, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.94/2.18  tff(f_50, axiom, (![A, B, C, D]: (v1_relat_1(D) => (r2_hidden(k4_tarski(A, B), k5_relat_1(k6_relat_1(C), D)) <=> (r2_hidden(A, C) & r2_hidden(k4_tarski(A, B), D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 5.94/2.18  tff(c_58, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.18  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.18  tff(c_54, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.18  tff(c_62, plain, (![D_27, A_28, B_29]: (r2_hidden(D_27, A_28) | ~r2_hidden(D_27, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.94/2.18  tff(c_66, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_62])).
% 5.94/2.18  tff(c_68, plain, (![D_32, B_33, A_34]: (r2_hidden(D_32, B_33) | ~r2_hidden(D_32, k3_xboole_0(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.94/2.18  tff(c_72, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_68])).
% 5.94/2.18  tff(c_46, plain, (![A_22, C_24]: (r2_hidden(k4_tarski(A_22, k1_funct_1(C_24, A_22)), C_24) | ~r2_hidden(A_22, k1_relat_1(C_24)) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.94/2.18  tff(c_42, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.94/2.18  tff(c_44, plain, (![A_21]: (v1_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.94/2.18  tff(c_38, plain, (![A_19, B_20]: (v1_funct_1(k5_relat_1(A_19, B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.94/2.18  tff(c_20, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.94/2.18  tff(c_223, plain, (![A_71, B_72, C_73, D_74]: (r2_hidden(k4_tarski(A_71, B_72), k5_relat_1(k6_relat_1(C_73), D_74)) | ~r2_hidden(k4_tarski(A_71, B_72), D_74) | ~r2_hidden(A_71, C_73) | ~v1_relat_1(D_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.94/2.18  tff(c_48, plain, (![C_24, A_22, B_23]: (k1_funct_1(C_24, A_22)=B_23 | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.94/2.18  tff(c_3338, plain, (![C_285, D_286, A_287, B_288]: (k1_funct_1(k5_relat_1(k6_relat_1(C_285), D_286), A_287)=B_288 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_285), D_286)) | ~v1_relat_1(k5_relat_1(k6_relat_1(C_285), D_286)) | ~r2_hidden(k4_tarski(A_287, B_288), D_286) | ~r2_hidden(A_287, C_285) | ~v1_relat_1(D_286))), inference(resolution, [status(thm)], [c_223, c_48])).
% 5.94/2.18  tff(c_3341, plain, (![C_285, B_8, A_287, B_288]: (k1_funct_1(k5_relat_1(k6_relat_1(C_285), B_8), A_287)=B_288 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_285), B_8)) | ~r2_hidden(k4_tarski(A_287, B_288), B_8) | ~r2_hidden(A_287, C_285) | ~v1_relat_1(B_8) | ~v1_relat_1(k6_relat_1(C_285)))), inference(resolution, [status(thm)], [c_20, c_3338])).
% 5.94/2.18  tff(c_3345, plain, (![C_289, B_290, A_291, B_292]: (k1_funct_1(k5_relat_1(k6_relat_1(C_289), B_290), A_291)=B_292 | ~v1_funct_1(k5_relat_1(k6_relat_1(C_289), B_290)) | ~r2_hidden(k4_tarski(A_291, B_292), B_290) | ~r2_hidden(A_291, C_289) | ~v1_relat_1(B_290))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_3341])).
% 5.94/2.18  tff(c_3348, plain, (![C_289, B_20, A_291, B_292]: (k1_funct_1(k5_relat_1(k6_relat_1(C_289), B_20), A_291)=B_292 | ~r2_hidden(k4_tarski(A_291, B_292), B_20) | ~r2_hidden(A_291, C_289) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(k6_relat_1(C_289)) | ~v1_relat_1(k6_relat_1(C_289)))), inference(resolution, [status(thm)], [c_38, c_3345])).
% 5.94/2.18  tff(c_3352, plain, (![C_293, B_294, A_295, B_296]: (k1_funct_1(k5_relat_1(k6_relat_1(C_293), B_294), A_295)=B_296 | ~r2_hidden(k4_tarski(A_295, B_296), B_294) | ~r2_hidden(A_295, C_293) | ~v1_funct_1(B_294) | ~v1_relat_1(B_294))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_3348])).
% 5.94/2.18  tff(c_3377, plain, (![C_297, C_298, A_299]: (k1_funct_1(k5_relat_1(k6_relat_1(C_297), C_298), A_299)=k1_funct_1(C_298, A_299) | ~r2_hidden(A_299, C_297) | ~r2_hidden(A_299, k1_relat_1(C_298)) | ~v1_funct_1(C_298) | ~v1_relat_1(C_298))), inference(resolution, [status(thm)], [c_46, c_3352])).
% 5.94/2.18  tff(c_52, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.94/2.18  tff(c_3393, plain, (~r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3377, c_52])).
% 5.94/2.18  tff(c_3408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_66, c_72, c_3393])).
% 5.94/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.94/2.18  
% 5.94/2.18  Inference rules
% 5.94/2.18  ----------------------
% 5.94/2.18  #Ref     : 0
% 5.94/2.18  #Sup     : 679
% 5.94/2.18  #Fact    : 0
% 5.94/2.18  #Define  : 0
% 5.94/2.18  #Split   : 0
% 5.94/2.18  #Chain   : 0
% 5.94/2.18  #Close   : 0
% 5.94/2.18  
% 5.94/2.18  Ordering : KBO
% 5.94/2.18  
% 5.94/2.18  Simplification rules
% 5.94/2.18  ----------------------
% 5.94/2.18  #Subsume      : 144
% 5.94/2.18  #Demod        : 278
% 5.94/2.18  #Tautology    : 55
% 5.94/2.18  #SimpNegUnit  : 0
% 5.94/2.18  #BackRed      : 0
% 5.94/2.18  
% 5.94/2.18  #Partial instantiations: 0
% 5.94/2.18  #Strategies tried      : 1
% 5.94/2.18  
% 5.94/2.18  Timing (in seconds)
% 5.94/2.18  ----------------------
% 5.94/2.19  Preprocessing        : 0.30
% 5.94/2.19  Parsing              : 0.17
% 5.94/2.19  CNF conversion       : 0.02
% 5.94/2.19  Main loop            : 1.12
% 5.94/2.19  Inferencing          : 0.43
% 5.94/2.19  Reduction            : 0.24
% 5.94/2.19  Demodulation         : 0.18
% 5.94/2.19  BG Simplification    : 0.06
% 5.94/2.19  Subsumption          : 0.30
% 5.94/2.19  Abstraction          : 0.09
% 5.94/2.19  MUC search           : 0.00
% 5.94/2.19  Cooper               : 0.00
% 5.94/2.19  Total                : 1.45
% 5.94/2.19  Index Insertion      : 0.00
% 5.94/2.19  Index Deletion       : 0.00
% 5.94/2.19  Index Matching       : 0.00
% 5.94/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
