%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:40 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   49 (  68 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 230 expanded)
%              Number of equality atoms :   38 (  91 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( ( k1_relat_1(B) = A
                & k1_relat_1(C) = A
                & r1_tarski(k2_relat_1(C),A)
                & v2_funct_1(B)
                & k5_relat_1(C,B) = B )
             => C = k6_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( r1_tarski(k2_relat_1(B),k1_relat_1(A))
                    & r1_tarski(k2_relat_1(C),k1_relat_1(A))
                    & k1_relat_1(B) = k1_relat_1(C)
                    & k5_relat_1(B,A) = k5_relat_1(C,A) )
                 => B = C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_1)).

tff(c_38,plain,(
    k6_relat_1('#skF_3') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_107,plain,(
    ! [A_31,B_32] :
      ( k5_relat_1(k6_relat_1(A_31),B_32) = B_32
      | ~ r1_tarski(k1_relat_1(B_32),A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_157,plain,(
    ! [B_35] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_35)),B_35) = B_35
      | ~ v1_relat_1(B_35) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_180,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_157])).

tff(c_194,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_180])).

tff(c_14,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_6] : v1_funct_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_3] : k2_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_52,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_46,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_40,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_357,plain,(
    ! [C_45,B_46,A_47] :
      ( C_45 = B_46
      | k5_relat_1(C_45,A_47) != k5_relat_1(B_46,A_47)
      | k1_relat_1(C_45) != k1_relat_1(B_46)
      | ~ r1_tarski(k2_relat_1(C_45),k1_relat_1(A_47))
      | ~ r1_tarski(k2_relat_1(B_46),k1_relat_1(A_47))
      | ~ v1_funct_1(C_45)
      | ~ v1_relat_1(C_45)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46)
      | ~ v2_funct_1(A_47)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_391,plain,(
    ! [B_46] :
      ( B_46 = '#skF_5'
      | k5_relat_1(B_46,'#skF_4') != '#skF_4'
      | k1_relat_1(B_46) != k1_relat_1('#skF_5')
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_46),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46)
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_357])).

tff(c_428,plain,(
    ! [B_50] :
      ( B_50 = '#skF_5'
      | k5_relat_1(B_50,'#skF_4') != '#skF_4'
      | k1_relat_1(B_50) != '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_50),'#skF_3')
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_52,c_50,c_48,c_44,c_48,c_46,c_391])).

tff(c_439,plain,(
    ! [A_3] :
      ( k6_relat_1(A_3) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_3),'#skF_4') != '#skF_4'
      | k1_relat_1(k6_relat_1(A_3)) != '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3')
      | ~ v1_funct_1(k6_relat_1(A_3))
      | ~ v1_relat_1(k6_relat_1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_428])).

tff(c_452,plain,(
    ! [A_51] :
      ( k6_relat_1(A_51) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_51),'#skF_4') != '#skF_4'
      | A_51 != '#skF_3'
      | ~ r1_tarski(A_51,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16,c_8,c_439])).

tff(c_458,plain,
    ( k6_relat_1('#skF_3') = '#skF_5'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_452])).

tff(c_466,plain,(
    k6_relat_1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_458])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.32  
% 2.76/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.32  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.76/1.32  
% 2.76/1.32  %Foreground sorts:
% 2.76/1.32  
% 2.76/1.32  
% 2.76/1.32  %Background operators:
% 2.76/1.32  
% 2.76/1.32  
% 2.76/1.32  %Foreground operators:
% 2.76/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.76/1.32  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.76/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.76/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.76/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.32  
% 2.76/1.33  tff(f_93, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_funct_1)).
% 2.76/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.76/1.33  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.76/1.33  tff(f_45, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.76/1.33  tff(f_35, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.76/1.33  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((r1_tarski(k2_relat_1(B), k1_relat_1(A)) & r1_tarski(k2_relat_1(C), k1_relat_1(A))) & (k1_relat_1(B) = k1_relat_1(C))) & (k5_relat_1(B, A) = k5_relat_1(C, A))) => (B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_1)).
% 2.76/1.33  tff(c_38, plain, (k6_relat_1('#skF_3')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.33  tff(c_56, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_48, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_107, plain, (![A_31, B_32]: (k5_relat_1(k6_relat_1(A_31), B_32)=B_32 | ~r1_tarski(k1_relat_1(B_32), A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.33  tff(c_157, plain, (![B_35]: (k5_relat_1(k6_relat_1(k1_relat_1(B_35)), B_35)=B_35 | ~v1_relat_1(B_35))), inference(resolution, [status(thm)], [c_6, c_107])).
% 2.76/1.33  tff(c_180, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_157])).
% 2.76/1.33  tff(c_194, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_180])).
% 2.76/1.33  tff(c_14, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.33  tff(c_16, plain, (![A_6]: (v1_funct_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.33  tff(c_8, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.33  tff(c_10, plain, (![A_3]: (k2_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.33  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_42, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_52, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_44, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_46, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_40, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.76/1.33  tff(c_357, plain, (![C_45, B_46, A_47]: (C_45=B_46 | k5_relat_1(C_45, A_47)!=k5_relat_1(B_46, A_47) | k1_relat_1(C_45)!=k1_relat_1(B_46) | ~r1_tarski(k2_relat_1(C_45), k1_relat_1(A_47)) | ~r1_tarski(k2_relat_1(B_46), k1_relat_1(A_47)) | ~v1_funct_1(C_45) | ~v1_relat_1(C_45) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46) | ~v2_funct_1(A_47) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.76/1.33  tff(c_391, plain, (![B_46]: (B_46='#skF_5' | k5_relat_1(B_46, '#skF_4')!='#skF_4' | k1_relat_1(B_46)!=k1_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_46), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(B_46) | ~v1_relat_1(B_46) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_357])).
% 2.76/1.33  tff(c_428, plain, (![B_50]: (B_50='#skF_5' | k5_relat_1(B_50, '#skF_4')!='#skF_4' | k1_relat_1(B_50)!='#skF_3' | ~r1_tarski(k2_relat_1(B_50), '#skF_3') | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_52, c_50, c_48, c_44, c_48, c_46, c_391])).
% 2.76/1.33  tff(c_439, plain, (![A_3]: (k6_relat_1(A_3)='#skF_5' | k5_relat_1(k6_relat_1(A_3), '#skF_4')!='#skF_4' | k1_relat_1(k6_relat_1(A_3))!='#skF_3' | ~r1_tarski(A_3, '#skF_3') | ~v1_funct_1(k6_relat_1(A_3)) | ~v1_relat_1(k6_relat_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_428])).
% 2.76/1.33  tff(c_452, plain, (![A_51]: (k6_relat_1(A_51)='#skF_5' | k5_relat_1(k6_relat_1(A_51), '#skF_4')!='#skF_4' | A_51!='#skF_3' | ~r1_tarski(A_51, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16, c_8, c_439])).
% 2.76/1.33  tff(c_458, plain, (k6_relat_1('#skF_3')='#skF_5' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_194, c_452])).
% 2.76/1.33  tff(c_466, plain, (k6_relat_1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_458])).
% 2.76/1.33  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_466])).
% 2.76/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.33  
% 2.76/1.33  Inference rules
% 2.76/1.33  ----------------------
% 2.76/1.33  #Ref     : 1
% 2.76/1.33  #Sup     : 88
% 2.76/1.33  #Fact    : 0
% 2.76/1.33  #Define  : 0
% 2.76/1.33  #Split   : 2
% 2.76/1.33  #Chain   : 0
% 2.76/1.33  #Close   : 0
% 2.76/1.33  
% 2.76/1.33  Ordering : KBO
% 2.76/1.33  
% 2.76/1.33  Simplification rules
% 2.76/1.33  ----------------------
% 2.76/1.33  #Subsume      : 0
% 2.76/1.33  #Demod        : 193
% 2.76/1.33  #Tautology    : 49
% 2.76/1.33  #SimpNegUnit  : 1
% 2.76/1.33  #BackRed      : 0
% 2.76/1.33  
% 2.76/1.33  #Partial instantiations: 0
% 2.76/1.33  #Strategies tried      : 1
% 2.76/1.33  
% 2.76/1.33  Timing (in seconds)
% 2.76/1.33  ----------------------
% 2.76/1.33  Preprocessing        : 0.30
% 2.76/1.33  Parsing              : 0.15
% 2.76/1.33  CNF conversion       : 0.02
% 2.76/1.33  Main loop            : 0.27
% 2.76/1.33  Inferencing          : 0.09
% 2.76/1.33  Reduction            : 0.09
% 2.76/1.33  Demodulation         : 0.07
% 2.76/1.33  BG Simplification    : 0.02
% 2.76/1.33  Subsumption          : 0.06
% 2.76/1.33  Abstraction          : 0.02
% 2.76/1.34  MUC search           : 0.00
% 2.76/1.34  Cooper               : 0.00
% 2.76/1.34  Total                : 0.60
% 2.76/1.34  Index Insertion      : 0.00
% 2.76/1.34  Index Deletion       : 0.00
% 2.76/1.34  Index Matching       : 0.00
% 2.76/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
