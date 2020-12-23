%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:42 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   55 (  82 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :  118 ( 261 expanded)
%              Number of equality atoms :   36 (  96 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_102,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_funct_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k5_relat_1(B,k6_relat_1(A)),B)
        & r1_tarski(k5_relat_1(k6_relat_1(A),B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_funct_1)).

tff(c_40,plain,(
    k6_relat_1('#skF_3') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_27)),A_27) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k5_relat_1(k6_relat_1(A_5),B_6),B_6)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_98,plain,(
    ! [A_27] :
      ( r1_tarski(A_27,A_27)
      | ~ v1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_10])).

tff(c_182,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k2_relat_1(A_39),k2_relat_1(B_40))
      | ~ r1_tarski(A_39,B_40)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_185,plain,(
    ! [A_4,B_40] :
      ( r1_tarski(A_4,k2_relat_1(B_40))
      | ~ r1_tarski(k6_relat_1(A_4),B_40)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_182])).

tff(c_193,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,k2_relat_1(B_42))
      | ~ r1_tarski(k6_relat_1(A_41),B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_185])).

tff(c_197,plain,(
    ! [A_41] :
      ( r1_tarski(A_41,k2_relat_1(k6_relat_1(A_41)))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_98,c_193])).

tff(c_203,plain,(
    ! [A_41] : r1_tarski(A_41,A_41) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_8,c_197])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_50,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_110,plain,
    ( k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_92])).

tff(c_118,plain,(
    k5_relat_1(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_110])).

tff(c_18,plain,(
    ! [A_8] : v1_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    k5_relat_1('#skF_5','#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_439,plain,(
    ! [C_68,B_69,A_70] :
      ( C_68 = B_69
      | k5_relat_1(C_68,A_70) != k5_relat_1(B_69,A_70)
      | k1_relat_1(C_68) != k1_relat_1(B_69)
      | ~ r1_tarski(k2_relat_1(C_68),k1_relat_1(A_70))
      | ~ r1_tarski(k2_relat_1(B_69),k1_relat_1(A_70))
      | ~ v1_funct_1(C_68)
      | ~ v1_relat_1(C_68)
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v2_funct_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_461,plain,(
    ! [B_69] :
      ( B_69 = '#skF_5'
      | k5_relat_1(B_69,'#skF_4') != '#skF_4'
      | k1_relat_1(B_69) != k1_relat_1('#skF_5')
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_69),k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_439])).

tff(c_485,plain,(
    ! [B_72] :
      ( B_72 = '#skF_5'
      | k5_relat_1(B_72,'#skF_4') != '#skF_4'
      | k1_relat_1(B_72) != '#skF_3'
      | ~ r1_tarski(k2_relat_1(B_72),'#skF_3')
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_44,c_54,c_52,c_50,c_46,c_50,c_48,c_461])).

tff(c_500,plain,(
    ! [A_4] :
      ( k6_relat_1(A_4) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_4),'#skF_4') != '#skF_4'
      | k1_relat_1(k6_relat_1(A_4)) != '#skF_3'
      | ~ r1_tarski(A_4,'#skF_3')
      | ~ v1_funct_1(k6_relat_1(A_4))
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_485])).

tff(c_514,plain,(
    ! [A_73] :
      ( k6_relat_1(A_73) = '#skF_5'
      | k5_relat_1(k6_relat_1(A_73),'#skF_4') != '#skF_4'
      | A_73 != '#skF_3'
      | ~ r1_tarski(A_73,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_6,c_500])).

tff(c_517,plain,
    ( k6_relat_1('#skF_3') = '#skF_5'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_514])).

tff(c_524,plain,(
    k6_relat_1('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_517])).

tff(c_526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.39  
% 2.89/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.40  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.89/1.40  
% 2.89/1.40  %Foreground sorts:
% 2.89/1.40  
% 2.89/1.40  
% 2.89/1.40  %Background operators:
% 2.89/1.40  
% 2.89/1.40  
% 2.89/1.40  %Foreground operators:
% 2.89/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.89/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.89/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.89/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.89/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.40  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.89/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.40  
% 2.89/1.41  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) & r1_tarski(k2_relat_1(C), A)) & v2_funct_1(B)) & (k5_relat_1(C, B) = B)) => (C = k6_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_funct_1)).
% 2.89/1.41  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.89/1.41  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.89/1.41  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 2.89/1.41  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k5_relat_1(B, k6_relat_1(A)), B) & r1_tarski(k5_relat_1(k6_relat_1(A), B), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 2.89/1.41  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.89/1.41  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((((r1_tarski(k2_relat_1(B), k1_relat_1(A)) & r1_tarski(k2_relat_1(C), k1_relat_1(A))) & (k1_relat_1(B) = k1_relat_1(C))) & (k5_relat_1(B, A) = k5_relat_1(C, A))) => (B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_funct_1)).
% 2.89/1.41  tff(c_40, plain, (k6_relat_1('#skF_3')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_16, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.41  tff(c_8, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.89/1.41  tff(c_92, plain, (![A_27]: (k5_relat_1(k6_relat_1(k1_relat_1(A_27)), A_27)=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.89/1.41  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k5_relat_1(k6_relat_1(A_5), B_6), B_6) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.89/1.41  tff(c_98, plain, (![A_27]: (r1_tarski(A_27, A_27) | ~v1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_92, c_10])).
% 2.89/1.41  tff(c_182, plain, (![A_39, B_40]: (r1_tarski(k2_relat_1(A_39), k2_relat_1(B_40)) | ~r1_tarski(A_39, B_40) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.89/1.41  tff(c_185, plain, (![A_4, B_40]: (r1_tarski(A_4, k2_relat_1(B_40)) | ~r1_tarski(k6_relat_1(A_4), B_40) | ~v1_relat_1(B_40) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_182])).
% 2.89/1.41  tff(c_193, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_relat_1(B_42)) | ~r1_tarski(k6_relat_1(A_41), B_42) | ~v1_relat_1(B_42))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_185])).
% 2.89/1.41  tff(c_197, plain, (![A_41]: (r1_tarski(A_41, k2_relat_1(k6_relat_1(A_41))) | ~v1_relat_1(k6_relat_1(A_41)))), inference(resolution, [status(thm)], [c_98, c_193])).
% 2.89/1.41  tff(c_203, plain, (![A_41]: (r1_tarski(A_41, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_8, c_197])).
% 2.89/1.41  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_50, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_110, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50, c_92])).
% 2.89/1.41  tff(c_118, plain, (k5_relat_1(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_110])).
% 2.89/1.41  tff(c_18, plain, (![A_8]: (v1_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.89/1.41  tff(c_6, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.89/1.41  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_44, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_54, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_46, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_48, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_42, plain, (k5_relat_1('#skF_5', '#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.89/1.41  tff(c_439, plain, (![C_68, B_69, A_70]: (C_68=B_69 | k5_relat_1(C_68, A_70)!=k5_relat_1(B_69, A_70) | k1_relat_1(C_68)!=k1_relat_1(B_69) | ~r1_tarski(k2_relat_1(C_68), k1_relat_1(A_70)) | ~r1_tarski(k2_relat_1(B_69), k1_relat_1(A_70)) | ~v1_funct_1(C_68) | ~v1_relat_1(C_68) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v2_funct_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.89/1.41  tff(c_461, plain, (![B_69]: (B_69='#skF_5' | k5_relat_1(B_69, '#skF_4')!='#skF_4' | k1_relat_1(B_69)!=k1_relat_1('#skF_5') | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_69), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_439])).
% 2.89/1.41  tff(c_485, plain, (![B_72]: (B_72='#skF_5' | k5_relat_1(B_72, '#skF_4')!='#skF_4' | k1_relat_1(B_72)!='#skF_3' | ~r1_tarski(k2_relat_1(B_72), '#skF_3') | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_44, c_54, c_52, c_50, c_46, c_50, c_48, c_461])).
% 2.89/1.41  tff(c_500, plain, (![A_4]: (k6_relat_1(A_4)='#skF_5' | k5_relat_1(k6_relat_1(A_4), '#skF_4')!='#skF_4' | k1_relat_1(k6_relat_1(A_4))!='#skF_3' | ~r1_tarski(A_4, '#skF_3') | ~v1_funct_1(k6_relat_1(A_4)) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_485])).
% 2.89/1.41  tff(c_514, plain, (![A_73]: (k6_relat_1(A_73)='#skF_5' | k5_relat_1(k6_relat_1(A_73), '#skF_4')!='#skF_4' | A_73!='#skF_3' | ~r1_tarski(A_73, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_6, c_500])).
% 2.89/1.41  tff(c_517, plain, (k6_relat_1('#skF_3')='#skF_5' | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_118, c_514])).
% 2.89/1.41  tff(c_524, plain, (k6_relat_1('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_517])).
% 2.89/1.41  tff(c_526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_524])).
% 2.89/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.41  
% 2.89/1.41  Inference rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Ref     : 1
% 2.89/1.41  #Sup     : 96
% 2.89/1.41  #Fact    : 0
% 2.89/1.41  #Define  : 0
% 2.89/1.41  #Split   : 1
% 2.89/1.41  #Chain   : 0
% 2.89/1.41  #Close   : 0
% 2.89/1.41  
% 2.89/1.41  Ordering : KBO
% 2.89/1.41  
% 2.89/1.41  Simplification rules
% 2.89/1.41  ----------------------
% 2.89/1.41  #Subsume      : 3
% 2.89/1.41  #Demod        : 175
% 2.89/1.41  #Tautology    : 47
% 2.89/1.41  #SimpNegUnit  : 1
% 2.89/1.41  #BackRed      : 0
% 2.89/1.41  
% 2.89/1.41  #Partial instantiations: 0
% 2.89/1.41  #Strategies tried      : 1
% 2.89/1.41  
% 2.89/1.41  Timing (in seconds)
% 2.89/1.41  ----------------------
% 2.89/1.41  Preprocessing        : 0.33
% 2.89/1.41  Parsing              : 0.17
% 2.89/1.41  CNF conversion       : 0.02
% 2.89/1.41  Main loop            : 0.32
% 2.89/1.41  Inferencing          : 0.12
% 2.89/1.41  Reduction            : 0.10
% 2.89/1.41  Demodulation         : 0.07
% 2.89/1.41  BG Simplification    : 0.02
% 2.89/1.41  Subsumption          : 0.06
% 2.89/1.41  Abstraction          : 0.02
% 2.89/1.41  MUC search           : 0.00
% 2.89/1.41  Cooper               : 0.00
% 2.89/1.41  Total                : 0.67
% 2.89/1.41  Index Insertion      : 0.00
% 2.89/1.41  Index Deletion       : 0.00
% 2.89/1.41  Index Matching       : 0.00
% 2.89/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
