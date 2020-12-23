%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:43 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 214 expanded)
%              Number of equality atoms :    8 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_207,plain,(
    ! [A_73,C_74,B_75] :
      ( ~ r2_hidden(A_73,C_74)
      | ~ r1_xboole_0(k2_tarski(A_73,B_75),C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_212,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_207])).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_178,plain,(
    ! [B_70,A_71] :
      ( ~ r1_xboole_0(B_70,A_71)
      | ~ r1_tarski(B_70,A_71)
      | v1_xboole_0(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_183,plain,(
    ! [A_72] :
      ( ~ r1_tarski(A_72,k1_xboole_0)
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_10,c_178])).

tff(c_188,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_183])).

tff(c_28,plain,(
    ! [A_37] :
      ( v1_relat_1(A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_206,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_188,c_28])).

tff(c_105,plain,(
    ! [B_62,A_63] :
      ( ~ r1_xboole_0(B_62,A_63)
      | ~ r1_tarski(B_62,A_63)
      | v1_xboole_0(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [A_64] :
      ( ~ r1_tarski(A_64,k1_xboole_0)
      | v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_10,c_105])).

tff(c_115,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_110])).

tff(c_51,plain,(
    ! [A_55] :
      ( v1_xboole_0(k1_relat_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_128,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_115,c_61])).

tff(c_30,plain,(
    ! [A_38] :
      ( v1_xboole_0(k1_relat_1(A_38))
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_73,plain,(
    ! [A_58] :
      ( k1_relat_1(A_58) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_80,plain,(
    ! [A_61] :
      ( k1_relat_1(k1_relat_1(A_61)) = k1_xboole_0
      | ~ v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_30,c_73])).

tff(c_32,plain,(
    ! [A_39] :
      ( v1_funct_1(A_39)
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_62,plain,(
    ! [A_55] :
      ( v1_funct_1(k1_relat_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_51,c_32])).

tff(c_89,plain,(
    ! [A_61] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_61))
      | ~ v1_xboole_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_62])).

tff(c_164,plain,(
    ! [A_69] :
      ( ~ v1_xboole_0(k1_relat_1(A_69))
      | ~ v1_xboole_0(A_69) ) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_167,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_164])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_167])).

tff(c_177,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_201,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_188,c_61])).

tff(c_294,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),k1_relat_1(B_105))
      | v5_funct_1(B_105,A_104)
      | ~ v1_funct_1(B_105)
      | ~ v1_relat_1(B_105)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_297,plain,(
    ! [A_104] :
      ( r2_hidden('#skF_1'(A_104,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_104)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_294])).

tff(c_302,plain,(
    ! [A_104] :
      ( r2_hidden('#skF_1'(A_104,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_104)
      | ~ v1_funct_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_177,c_297])).

tff(c_305,plain,(
    ! [A_106] :
      ( v5_funct_1(k1_xboole_0,A_106)
      | ~ v1_funct_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_302])).

tff(c_40,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_308,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_305,c_40])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:25:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.25  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.17/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.25  
% 2.17/1.26  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.17/1.26  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.17/1.26  tff(f_62, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.17/1.26  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.26  tff(f_45, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.17/1.26  tff(f_66, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.17/1.26  tff(f_70, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.17/1.26  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.17/1.26  tff(f_74, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.17/1.26  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.17/1.26  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.26  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.26  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.26  tff(c_207, plain, (![A_73, C_74, B_75]: (~r2_hidden(A_73, C_74) | ~r1_xboole_0(k2_tarski(A_73, B_75), C_74))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.26  tff(c_212, plain, (![A_73]: (~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_207])).
% 2.17/1.26  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.26  tff(c_178, plain, (![B_70, A_71]: (~r1_xboole_0(B_70, A_71) | ~r1_tarski(B_70, A_71) | v1_xboole_0(B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.26  tff(c_183, plain, (![A_72]: (~r1_tarski(A_72, k1_xboole_0) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_10, c_178])).
% 2.17/1.26  tff(c_188, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_183])).
% 2.17/1.26  tff(c_28, plain, (![A_37]: (v1_relat_1(A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.26  tff(c_206, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_188, c_28])).
% 2.17/1.26  tff(c_105, plain, (![B_62, A_63]: (~r1_xboole_0(B_62, A_63) | ~r1_tarski(B_62, A_63) | v1_xboole_0(B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.26  tff(c_110, plain, (![A_64]: (~r1_tarski(A_64, k1_xboole_0) | v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_10, c_105])).
% 2.17/1.26  tff(c_115, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_110])).
% 2.17/1.26  tff(c_51, plain, (![A_55]: (v1_xboole_0(k1_relat_1(A_55)) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.26  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.26  tff(c_61, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.17/1.26  tff(c_128, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_115, c_61])).
% 2.17/1.26  tff(c_30, plain, (![A_38]: (v1_xboole_0(k1_relat_1(A_38)) | ~v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.26  tff(c_73, plain, (![A_58]: (k1_relat_1(A_58)=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_51, c_2])).
% 2.17/1.26  tff(c_80, plain, (![A_61]: (k1_relat_1(k1_relat_1(A_61))=k1_xboole_0 | ~v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_30, c_73])).
% 2.17/1.26  tff(c_32, plain, (![A_39]: (v1_funct_1(A_39) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.26  tff(c_62, plain, (![A_55]: (v1_funct_1(k1_relat_1(A_55)) | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_51, c_32])).
% 2.17/1.26  tff(c_89, plain, (![A_61]: (v1_funct_1(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_61)) | ~v1_xboole_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_80, c_62])).
% 2.17/1.26  tff(c_164, plain, (![A_69]: (~v1_xboole_0(k1_relat_1(A_69)) | ~v1_xboole_0(A_69))), inference(splitLeft, [status(thm)], [c_89])).
% 2.17/1.26  tff(c_167, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_164])).
% 2.17/1.26  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_167])).
% 2.17/1.26  tff(c_177, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_89])).
% 2.17/1.26  tff(c_201, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_188, c_61])).
% 2.17/1.26  tff(c_294, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104, B_105), k1_relat_1(B_105)) | v5_funct_1(B_105, A_104) | ~v1_funct_1(B_105) | ~v1_relat_1(B_105) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.17/1.26  tff(c_297, plain, (![A_104]: (r2_hidden('#skF_1'(A_104, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_104) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(superposition, [status(thm), theory('equality')], [c_201, c_294])).
% 2.17/1.26  tff(c_302, plain, (![A_104]: (r2_hidden('#skF_1'(A_104, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_104) | ~v1_funct_1(A_104) | ~v1_relat_1(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_206, c_177, c_297])).
% 2.17/1.26  tff(c_305, plain, (![A_106]: (v5_funct_1(k1_xboole_0, A_106) | ~v1_funct_1(A_106) | ~v1_relat_1(A_106))), inference(negUnitSimplification, [status(thm)], [c_212, c_302])).
% 2.17/1.26  tff(c_40, plain, (~v5_funct_1(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.17/1.26  tff(c_308, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_305, c_40])).
% 2.17/1.26  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_308])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 56
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 1
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 0
% 2.17/1.26  #Demod        : 29
% 2.17/1.26  #Tautology    : 35
% 2.17/1.26  #SimpNegUnit  : 2
% 2.17/1.26  #BackRed      : 0
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.26  
% 2.17/1.26  Timing (in seconds)
% 2.17/1.26  ----------------------
% 2.17/1.27  Preprocessing        : 0.31
% 2.17/1.27  Parsing              : 0.16
% 2.17/1.27  CNF conversion       : 0.02
% 2.17/1.27  Main loop            : 0.19
% 2.17/1.27  Inferencing          : 0.08
% 2.17/1.27  Reduction            : 0.06
% 2.17/1.27  Demodulation         : 0.04
% 2.17/1.27  BG Simplification    : 0.02
% 2.17/1.27  Subsumption          : 0.03
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.53
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
