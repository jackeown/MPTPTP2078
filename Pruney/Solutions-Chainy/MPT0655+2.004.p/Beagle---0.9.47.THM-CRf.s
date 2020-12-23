%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:59 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   55 (  96 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 ( 295 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k2_relat_1(B)) )
       => ( A = k1_funct_1(B,k1_funct_1(k2_funct_1(B),A))
          & A = k1_funct_1(k5_relat_1(k2_funct_1(B),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_8] :
      ( v1_funct_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k2_funct_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_33,plain,(
    ! [A_14] :
      ( '#skF_2'(A_14) != '#skF_1'(A_14)
      | v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_24,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_37,plain,
    ( '#skF_2'(k2_funct_1('#skF_3')) != '#skF_1'(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_33,c_24])).

tff(c_48,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_37])).

tff(c_51,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_51])).

tff(c_56,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_3'))
    | '#skF_2'(k2_funct_1('#skF_3')) != '#skF_1'(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_58,plain,(
    '#skF_2'(k2_funct_1('#skF_3')) != '#skF_1'(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_26,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_57,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_37])).

tff(c_18,plain,(
    ! [A_9] :
      ( k1_relat_1(k2_funct_1(A_9)) = k2_relat_1(A_9)
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_1'(A_18),k1_relat_1(A_18))
      | v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_74,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_1'(k2_funct_1(A_9)),k2_relat_1(A_9))
      | v2_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(k2_funct_1(A_9))
      | ~ v1_relat_1(k2_funct_1(A_9))
      | ~ v2_funct_1(A_9)
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_71])).

tff(c_59,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_65,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(k2_funct_1(A_17)),k2_relat_1(A_17))
      | v2_funct_1(k2_funct_1(A_17))
      | ~ v1_funct_1(k2_funct_1(A_17))
      | ~ v1_relat_1(k2_funct_1(A_17))
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_8])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( k1_funct_1(B_11,k1_funct_1(k2_funct_1(B_11),A_10)) = A_10
      | ~ r2_hidden(A_10,k2_relat_1(B_11))
      | ~ v2_funct_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_84,plain,(
    ! [B_20,A_21] :
      ( k1_funct_1(B_20,k1_funct_1(k2_funct_1(B_20),A_21)) = A_21
      | ~ r2_hidden(A_21,k2_relat_1(B_20))
      | ~ v2_funct_1(B_20)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_155,plain,(
    ! [B_29] :
      ( k1_funct_1(B_29,k1_funct_1(k2_funct_1(B_29),'#skF_1'(k2_funct_1(B_29)))) = '#skF_2'(k2_funct_1(B_29))
      | ~ r2_hidden('#skF_2'(k2_funct_1(B_29)),k2_relat_1(B_29))
      | ~ v2_funct_1(B_29)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | v2_funct_1(k2_funct_1(B_29))
      | ~ v1_funct_1(k2_funct_1(B_29))
      | ~ v1_relat_1(k2_funct_1(B_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_227,plain,(
    ! [B_37] :
      ( '#skF_2'(k2_funct_1(B_37)) = '#skF_1'(k2_funct_1(B_37))
      | ~ r2_hidden('#skF_2'(k2_funct_1(B_37)),k2_relat_1(B_37))
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | v2_funct_1(k2_funct_1(B_37))
      | ~ v1_funct_1(k2_funct_1(B_37))
      | ~ v1_relat_1(k2_funct_1(B_37))
      | ~ r2_hidden('#skF_1'(k2_funct_1(B_37)),k2_relat_1(B_37))
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_155])).

tff(c_235,plain,(
    ! [A_38] :
      ( '#skF_2'(k2_funct_1(A_38)) = '#skF_1'(k2_funct_1(A_38))
      | ~ r2_hidden('#skF_1'(k2_funct_1(A_38)),k2_relat_1(A_38))
      | v2_funct_1(k2_funct_1(A_38))
      | ~ v1_funct_1(k2_funct_1(A_38))
      | ~ v1_relat_1(k2_funct_1(A_38))
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(resolution,[status(thm)],[c_65,c_227])).

tff(c_243,plain,(
    ! [A_39] :
      ( '#skF_2'(k2_funct_1(A_39)) = '#skF_1'(k2_funct_1(A_39))
      | v2_funct_1(k2_funct_1(A_39))
      | ~ v1_funct_1(k2_funct_1(A_39))
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_74,c_235])).

tff(c_246,plain,
    ( '#skF_2'(k2_funct_1('#skF_3')) = '#skF_1'(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_243,c_24])).

tff(c_249,plain,
    ( '#skF_2'(k2_funct_1('#skF_3')) = '#skF_1'(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_57,c_246])).

tff(c_250,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_249])).

tff(c_253,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_250])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_253])).

tff(c_258,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_262,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_258])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  
% 2.57/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.36  %$ r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_3
% 2.57/1.36  
% 2.57/1.36  %Foreground sorts:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Background operators:
% 2.57/1.36  
% 2.57/1.36  
% 2.57/1.36  %Foreground operators:
% 2.57/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.57/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.57/1.36  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.57/1.36  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.57/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.57/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.57/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.36  
% 2.74/1.38  tff(f_79, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_1)).
% 2.74/1.38  tff(f_48, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.74/1.38  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.74/1.38  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.74/1.38  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k2_relat_1(B))) => ((A = k1_funct_1(B, k1_funct_1(k2_funct_1(B), A))) & (A = k1_funct_1(k5_relat_1(k2_funct_1(B), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_funct_1)).
% 2.74/1.38  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.38  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.38  tff(c_12, plain, (![A_8]: (v1_funct_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.74/1.38  tff(c_14, plain, (![A_8]: (v1_relat_1(k2_funct_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.74/1.38  tff(c_33, plain, (![A_14]: ('#skF_2'(A_14)!='#skF_1'(A_14) | v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.38  tff(c_24, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.38  tff(c_37, plain, ('#skF_2'(k2_funct_1('#skF_3'))!='#skF_1'(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_33, c_24])).
% 2.74/1.38  tff(c_48, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_37])).
% 2.74/1.38  tff(c_51, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_48])).
% 2.74/1.38  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_51])).
% 2.74/1.38  tff(c_56, plain, (~v1_funct_1(k2_funct_1('#skF_3')) | '#skF_2'(k2_funct_1('#skF_3'))!='#skF_1'(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_37])).
% 2.74/1.38  tff(c_58, plain, ('#skF_2'(k2_funct_1('#skF_3'))!='#skF_1'(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 2.74/1.38  tff(c_26, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.74/1.38  tff(c_57, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_37])).
% 2.74/1.38  tff(c_18, plain, (![A_9]: (k1_relat_1(k2_funct_1(A_9))=k2_relat_1(A_9) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.38  tff(c_71, plain, (![A_18]: (r2_hidden('#skF_1'(A_18), k1_relat_1(A_18)) | v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.38  tff(c_74, plain, (![A_9]: (r2_hidden('#skF_1'(k2_funct_1(A_9)), k2_relat_1(A_9)) | v2_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(k2_funct_1(A_9)) | ~v1_relat_1(k2_funct_1(A_9)) | ~v2_funct_1(A_9) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_18, c_71])).
% 2.74/1.38  tff(c_59, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.38  tff(c_8, plain, (![A_1]: (r2_hidden('#skF_2'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.38  tff(c_65, plain, (![A_17]: (r2_hidden('#skF_2'(k2_funct_1(A_17)), k2_relat_1(A_17)) | v2_funct_1(k2_funct_1(A_17)) | ~v1_funct_1(k2_funct_1(A_17)) | ~v1_relat_1(k2_funct_1(A_17)) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_59, c_8])).
% 2.74/1.38  tff(c_22, plain, (![B_11, A_10]: (k1_funct_1(B_11, k1_funct_1(k2_funct_1(B_11), A_10))=A_10 | ~r2_hidden(A_10, k2_relat_1(B_11)) | ~v2_funct_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.38  tff(c_6, plain, (![A_1]: (k1_funct_1(A_1, '#skF_2'(A_1))=k1_funct_1(A_1, '#skF_1'(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.74/1.38  tff(c_84, plain, (![B_20, A_21]: (k1_funct_1(B_20, k1_funct_1(k2_funct_1(B_20), A_21))=A_21 | ~r2_hidden(A_21, k2_relat_1(B_20)) | ~v2_funct_1(B_20) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.38  tff(c_155, plain, (![B_29]: (k1_funct_1(B_29, k1_funct_1(k2_funct_1(B_29), '#skF_1'(k2_funct_1(B_29))))='#skF_2'(k2_funct_1(B_29)) | ~r2_hidden('#skF_2'(k2_funct_1(B_29)), k2_relat_1(B_29)) | ~v2_funct_1(B_29) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | v2_funct_1(k2_funct_1(B_29)) | ~v1_funct_1(k2_funct_1(B_29)) | ~v1_relat_1(k2_funct_1(B_29)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_84])).
% 2.74/1.38  tff(c_227, plain, (![B_37]: ('#skF_2'(k2_funct_1(B_37))='#skF_1'(k2_funct_1(B_37)) | ~r2_hidden('#skF_2'(k2_funct_1(B_37)), k2_relat_1(B_37)) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | v2_funct_1(k2_funct_1(B_37)) | ~v1_funct_1(k2_funct_1(B_37)) | ~v1_relat_1(k2_funct_1(B_37)) | ~r2_hidden('#skF_1'(k2_funct_1(B_37)), k2_relat_1(B_37)) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_22, c_155])).
% 2.74/1.38  tff(c_235, plain, (![A_38]: ('#skF_2'(k2_funct_1(A_38))='#skF_1'(k2_funct_1(A_38)) | ~r2_hidden('#skF_1'(k2_funct_1(A_38)), k2_relat_1(A_38)) | v2_funct_1(k2_funct_1(A_38)) | ~v1_funct_1(k2_funct_1(A_38)) | ~v1_relat_1(k2_funct_1(A_38)) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(resolution, [status(thm)], [c_65, c_227])).
% 2.74/1.38  tff(c_243, plain, (![A_39]: ('#skF_2'(k2_funct_1(A_39))='#skF_1'(k2_funct_1(A_39)) | v2_funct_1(k2_funct_1(A_39)) | ~v1_funct_1(k2_funct_1(A_39)) | ~v1_relat_1(k2_funct_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_74, c_235])).
% 2.74/1.38  tff(c_246, plain, ('#skF_2'(k2_funct_1('#skF_3'))='#skF_1'(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_243, c_24])).
% 2.74/1.38  tff(c_249, plain, ('#skF_2'(k2_funct_1('#skF_3'))='#skF_1'(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_57, c_246])).
% 2.74/1.38  tff(c_250, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_249])).
% 2.74/1.38  tff(c_253, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_250])).
% 2.74/1.38  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_253])).
% 2.74/1.38  tff(c_258, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_56])).
% 2.74/1.38  tff(c_262, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_258])).
% 2.74/1.38  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_262])).
% 2.74/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  Inference rules
% 2.74/1.38  ----------------------
% 2.74/1.38  #Ref     : 2
% 2.74/1.38  #Sup     : 55
% 2.74/1.38  #Fact    : 0
% 2.74/1.38  #Define  : 0
% 2.74/1.38  #Split   : 2
% 2.74/1.38  #Chain   : 0
% 2.74/1.38  #Close   : 0
% 2.74/1.38  
% 2.74/1.38  Ordering : KBO
% 2.74/1.38  
% 2.74/1.38  Simplification rules
% 2.74/1.38  ----------------------
% 2.74/1.38  #Subsume      : 4
% 2.74/1.38  #Demod        : 10
% 2.74/1.38  #Tautology    : 17
% 2.74/1.38  #SimpNegUnit  : 1
% 2.74/1.38  #BackRed      : 0
% 2.74/1.38  
% 2.74/1.38  #Partial instantiations: 0
% 2.74/1.38  #Strategies tried      : 1
% 2.74/1.38  
% 2.74/1.38  Timing (in seconds)
% 2.74/1.38  ----------------------
% 2.74/1.38  Preprocessing        : 0.34
% 2.74/1.38  Parsing              : 0.20
% 2.74/1.38  CNF conversion       : 0.02
% 2.74/1.38  Main loop            : 0.24
% 2.74/1.38  Inferencing          : 0.10
% 2.74/1.38  Reduction            : 0.06
% 2.74/1.38  Demodulation         : 0.05
% 2.74/1.38  BG Simplification    : 0.02
% 2.74/1.38  Subsumption          : 0.05
% 2.74/1.38  Abstraction          : 0.02
% 2.74/1.38  MUC search           : 0.00
% 2.74/1.38  Cooper               : 0.00
% 2.74/1.38  Total                : 0.61
% 2.74/1.38  Index Insertion      : 0.00
% 2.74/1.38  Index Deletion       : 0.00
% 2.74/1.38  Index Matching       : 0.00
% 2.74/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
