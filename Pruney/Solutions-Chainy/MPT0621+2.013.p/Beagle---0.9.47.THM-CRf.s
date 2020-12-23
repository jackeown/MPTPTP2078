%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:00 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 110 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :   95 ( 397 expanded)
%              Number of equality atoms :   68 ( 271 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_16,plain,(
    ! [A_6,B_10] :
      ( k1_relat_1('#skF_3'(A_6,B_10)) = A_6
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_6,B_10] :
      ( v1_funct_1('#skF_3'(A_6,B_10))
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_6,B_10] :
      ( v1_relat_1('#skF_3'(A_6,B_10))
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [C_33,B_34] :
      ( C_33 = B_34
      | k1_relat_1(C_33) != '#skF_4'
      | k1_relat_1(B_34) != '#skF_4'
      | ~ v1_funct_1(C_33)
      | ~ v1_relat_1(C_33)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_96,plain,(
    ! [B_43,A_44,B_45] :
      ( B_43 = '#skF_3'(A_44,B_45)
      | k1_relat_1('#skF_3'(A_44,B_45)) != '#skF_4'
      | k1_relat_1(B_43) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_44,B_45))
      | ~ v1_funct_1(B_43)
      | ~ v1_relat_1(B_43)
      | k1_xboole_0 = A_44 ) ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_100,plain,(
    ! [B_46,A_47,B_48] :
      ( B_46 = '#skF_3'(A_47,B_48)
      | k1_relat_1('#skF_3'(A_47,B_48)) != '#skF_4'
      | k1_relat_1(B_46) != '#skF_4'
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46)
      | k1_xboole_0 = A_47 ) ),
    inference(resolution,[status(thm)],[c_18,c_96])).

tff(c_104,plain,(
    ! [B_49,A_50,B_51] :
      ( B_49 = '#skF_3'(A_50,B_51)
      | A_50 != '#skF_4'
      | k1_relat_1(B_49) != '#skF_4'
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49)
      | k1_xboole_0 = A_50
      | k1_xboole_0 = A_50 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_100])).

tff(c_109,plain,(
    ! [A_54,B_55,A_52,B_53] :
      ( '#skF_3'(A_54,B_55) = '#skF_3'(A_52,B_53)
      | A_54 != '#skF_4'
      | k1_relat_1('#skF_3'(A_52,B_53)) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_52,B_53))
      | k1_xboole_0 = A_54
      | k1_xboole_0 = A_52 ) ),
    inference(resolution,[status(thm)],[c_20,c_104])).

tff(c_114,plain,(
    ! [A_58,B_59,A_56,B_57] :
      ( '#skF_3'(A_58,B_59) = '#skF_3'(A_56,B_57)
      | A_58 != '#skF_4'
      | k1_relat_1('#skF_3'(A_56,B_57)) != '#skF_4'
      | k1_xboole_0 = A_58
      | k1_xboole_0 = A_56 ) ),
    inference(resolution,[status(thm)],[c_18,c_109])).

tff(c_121,plain,(
    ! [A_62,B_63,A_60,B_61] :
      ( '#skF_3'(A_62,B_63) = '#skF_3'(A_60,B_61)
      | A_62 != '#skF_4'
      | A_60 != '#skF_4'
      | k1_xboole_0 = A_62
      | k1_xboole_0 = A_60
      | k1_xboole_0 = A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_114])).

tff(c_14,plain,(
    ! [A_6,B_10] :
      ( k2_relat_1('#skF_3'(A_6,B_10)) = k1_tarski(B_10)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_144,plain,(
    ! [A_62,B_63,B_61,A_60] :
      ( k2_relat_1('#skF_3'(A_62,B_63)) = k1_tarski(B_61)
      | k1_xboole_0 = A_60
      | A_62 != '#skF_4'
      | A_60 != '#skF_4'
      | k1_xboole_0 = A_62
      | k1_xboole_0 = A_60
      | k1_xboole_0 = A_60 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_14])).

tff(c_220,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_22])).

tff(c_238,plain,(
    ! [A_72,B_73,B_74] :
      ( k2_relat_1('#skF_3'(A_72,B_73)) = k1_tarski(B_74)
      | A_72 != '#skF_4'
      | k1_xboole_0 = A_72 ) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_255,plain,(
    ! [B_74,B_73,A_72] :
      ( k1_tarski(B_74) = k1_tarski(B_73)
      | k1_xboole_0 = A_72
      | A_72 != '#skF_4'
      | k1_xboole_0 = A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_14])).

tff(c_277,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_22])).

tff(c_294,plain,(
    ! [B_76,B_75] : k1_tarski(B_76) = k1_tarski(B_75) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_315,plain,(
    ! [B_75,B_76] : r2_hidden(B_75,k1_tarski(B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_4])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_348,plain,(
    ! [C_79,A_80] : C_79 = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_2])).

tff(c_414,plain,(
    ! [C_79] : C_79 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_22])).

tff(c_422,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:58:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  
% 2.29/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.32  %$ r2_hidden > v1_relat_1 > v1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.29/1.32  
% 2.29/1.32  %Foreground sorts:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Background operators:
% 2.29/1.32  
% 2.29/1.32  
% 2.29/1.32  %Foreground operators:
% 2.29/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.29/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.29/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.29/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.32  
% 2.29/1.33  tff(f_45, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.29/1.33  tff(f_64, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.29/1.33  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.29/1.33  tff(c_16, plain, (![A_6, B_10]: (k1_relat_1('#skF_3'(A_6, B_10))=A_6 | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.33  tff(c_18, plain, (![A_6, B_10]: (v1_funct_1('#skF_3'(A_6, B_10)) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.33  tff(c_20, plain, (![A_6, B_10]: (v1_relat_1('#skF_3'(A_6, B_10)) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.33  tff(c_61, plain, (![C_33, B_34]: (C_33=B_34 | k1_relat_1(C_33)!='#skF_4' | k1_relat_1(B_34)!='#skF_4' | ~v1_funct_1(C_33) | ~v1_relat_1(C_33) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.33  tff(c_96, plain, (![B_43, A_44, B_45]: (B_43='#skF_3'(A_44, B_45) | k1_relat_1('#skF_3'(A_44, B_45))!='#skF_4' | k1_relat_1(B_43)!='#skF_4' | ~v1_funct_1('#skF_3'(A_44, B_45)) | ~v1_funct_1(B_43) | ~v1_relat_1(B_43) | k1_xboole_0=A_44)), inference(resolution, [status(thm)], [c_20, c_61])).
% 2.29/1.33  tff(c_100, plain, (![B_46, A_47, B_48]: (B_46='#skF_3'(A_47, B_48) | k1_relat_1('#skF_3'(A_47, B_48))!='#skF_4' | k1_relat_1(B_46)!='#skF_4' | ~v1_funct_1(B_46) | ~v1_relat_1(B_46) | k1_xboole_0=A_47)), inference(resolution, [status(thm)], [c_18, c_96])).
% 2.29/1.33  tff(c_104, plain, (![B_49, A_50, B_51]: (B_49='#skF_3'(A_50, B_51) | A_50!='#skF_4' | k1_relat_1(B_49)!='#skF_4' | ~v1_funct_1(B_49) | ~v1_relat_1(B_49) | k1_xboole_0=A_50 | k1_xboole_0=A_50)), inference(superposition, [status(thm), theory('equality')], [c_16, c_100])).
% 2.29/1.33  tff(c_109, plain, (![A_54, B_55, A_52, B_53]: ('#skF_3'(A_54, B_55)='#skF_3'(A_52, B_53) | A_54!='#skF_4' | k1_relat_1('#skF_3'(A_52, B_53))!='#skF_4' | ~v1_funct_1('#skF_3'(A_52, B_53)) | k1_xboole_0=A_54 | k1_xboole_0=A_52)), inference(resolution, [status(thm)], [c_20, c_104])).
% 2.29/1.33  tff(c_114, plain, (![A_58, B_59, A_56, B_57]: ('#skF_3'(A_58, B_59)='#skF_3'(A_56, B_57) | A_58!='#skF_4' | k1_relat_1('#skF_3'(A_56, B_57))!='#skF_4' | k1_xboole_0=A_58 | k1_xboole_0=A_56)), inference(resolution, [status(thm)], [c_18, c_109])).
% 2.29/1.33  tff(c_121, plain, (![A_62, B_63, A_60, B_61]: ('#skF_3'(A_62, B_63)='#skF_3'(A_60, B_61) | A_62!='#skF_4' | A_60!='#skF_4' | k1_xboole_0=A_62 | k1_xboole_0=A_60 | k1_xboole_0=A_60)), inference(superposition, [status(thm), theory('equality')], [c_16, c_114])).
% 2.29/1.33  tff(c_14, plain, (![A_6, B_10]: (k2_relat_1('#skF_3'(A_6, B_10))=k1_tarski(B_10) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.29/1.33  tff(c_144, plain, (![A_62, B_63, B_61, A_60]: (k2_relat_1('#skF_3'(A_62, B_63))=k1_tarski(B_61) | k1_xboole_0=A_60 | A_62!='#skF_4' | A_60!='#skF_4' | k1_xboole_0=A_62 | k1_xboole_0=A_60 | k1_xboole_0=A_60)), inference(superposition, [status(thm), theory('equality')], [c_121, c_14])).
% 2.29/1.33  tff(c_220, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_144])).
% 2.29/1.33  tff(c_22, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.29/1.33  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_220, c_22])).
% 2.29/1.33  tff(c_238, plain, (![A_72, B_73, B_74]: (k2_relat_1('#skF_3'(A_72, B_73))=k1_tarski(B_74) | A_72!='#skF_4' | k1_xboole_0=A_72)), inference(splitRight, [status(thm)], [c_144])).
% 2.29/1.33  tff(c_255, plain, (![B_74, B_73, A_72]: (k1_tarski(B_74)=k1_tarski(B_73) | k1_xboole_0=A_72 | A_72!='#skF_4' | k1_xboole_0=A_72)), inference(superposition, [status(thm), theory('equality')], [c_238, c_14])).
% 2.29/1.33  tff(c_277, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_255])).
% 2.29/1.33  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_22])).
% 2.29/1.33  tff(c_294, plain, (![B_76, B_75]: (k1_tarski(B_76)=k1_tarski(B_75))), inference(splitRight, [status(thm)], [c_255])).
% 2.29/1.33  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.33  tff(c_315, plain, (![B_75, B_76]: (r2_hidden(B_75, k1_tarski(B_76)))), inference(superposition, [status(thm), theory('equality')], [c_294, c_4])).
% 2.29/1.33  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.33  tff(c_348, plain, (![C_79, A_80]: (C_79=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_2])).
% 2.29/1.33  tff(c_414, plain, (![C_79]: (C_79!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_348, c_22])).
% 2.29/1.33  tff(c_422, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_414])).
% 2.29/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  Inference rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Ref     : 3
% 2.29/1.33  #Sup     : 97
% 2.29/1.33  #Fact    : 0
% 2.29/1.33  #Define  : 0
% 2.29/1.33  #Split   : 2
% 2.29/1.33  #Chain   : 0
% 2.29/1.33  #Close   : 0
% 2.29/1.33  
% 2.29/1.33  Ordering : KBO
% 2.29/1.33  
% 2.29/1.33  Simplification rules
% 2.29/1.33  ----------------------
% 2.29/1.33  #Subsume      : 58
% 2.29/1.33  #Demod        : 53
% 2.29/1.33  #Tautology    : 32
% 2.29/1.33  #SimpNegUnit  : 2
% 2.29/1.33  #BackRed      : 13
% 2.29/1.33  
% 2.29/1.33  #Partial instantiations: 64
% 2.29/1.33  #Strategies tried      : 1
% 2.29/1.33  
% 2.29/1.33  Timing (in seconds)
% 2.29/1.33  ----------------------
% 2.29/1.33  Preprocessing        : 0.30
% 2.29/1.33  Parsing              : 0.15
% 2.29/1.33  CNF conversion       : 0.02
% 2.29/1.33  Main loop            : 0.25
% 2.29/1.33  Inferencing          : 0.10
% 2.29/1.33  Reduction            : 0.06
% 2.29/1.33  Demodulation         : 0.04
% 2.29/1.33  BG Simplification    : 0.02
% 2.29/1.33  Subsumption          : 0.06
% 2.29/1.33  Abstraction          : 0.02
% 2.29/1.33  MUC search           : 0.00
% 2.29/1.33  Cooper               : 0.00
% 2.29/1.33  Total                : 0.57
% 2.29/1.33  Index Insertion      : 0.00
% 2.29/1.33  Index Deletion       : 0.00
% 2.29/1.33  Index Matching       : 0.00
% 2.29/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
