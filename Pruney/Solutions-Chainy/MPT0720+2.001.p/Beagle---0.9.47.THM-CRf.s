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
% DateTime   : Thu Dec  3 10:05:51 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :   58 (  99 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 227 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B)
              & v5_funct_1(B,A) )
           => r1_tarski(k1_relat_1(B),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    v5_funct_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [C_43,B_44,A_45] :
      ( r2_hidden(C_43,B_44)
      | ~ r2_hidden(C_43,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_81,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48),B_49)
      | ~ r1_tarski(A_48,B_49)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_118,plain,(
    ! [B_52,A_53] :
      ( ~ v1_xboole_0(B_52)
      | ~ r1_tarski(A_53,B_52)
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_130,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(A_12)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_131,plain,(
    ! [A_12] : ~ v1_xboole_0(A_12) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_79,plain,(
    ! [A_3,B_44] :
      ( r2_hidden('#skF_1'(A_3),B_44)
      | ~ r1_tarski(A_3,B_44)
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_152,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59),B_60)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_79])).

tff(c_48,plain,(
    ! [B_33,A_34] :
      ( ~ r2_hidden(B_33,A_34)
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_51,plain,(
    ! [A_3] :
      ( ~ r2_hidden(A_3,'#skF_1'(A_3))
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_134,plain,(
    ! [A_3] : ~ r2_hidden(A_3,'#skF_1'(A_3)) ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_51])).

tff(c_169,plain,(
    ! [A_61] : ~ r1_tarski(A_61,'#skF_1'('#skF_1'(A_61))) ),
    inference(resolution,[status(thm)],[c_152,c_134])).

tff(c_174,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_169])).

tff(c_175,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_102,plain,(
    ! [A_50,B_51] :
      ( k1_funct_1(A_50,B_51) = k1_xboole_0
      | r2_hidden(B_51,k1_relat_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_7,A_50] :
      ( r1_tarski(A_7,k1_relat_1(A_50))
      | k1_funct_1(A_50,'#skF_2'(A_7,k1_relat_1(A_50))) = k1_xboole_0
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(resolution,[status(thm)],[c_102,c_10])).

tff(c_352,plain,(
    ! [B_85,C_86,A_87] :
      ( r2_hidden(k1_funct_1(B_85,C_86),k1_funct_1(A_87,C_86))
      | ~ r2_hidden(C_86,k1_relat_1(B_85))
      | ~ v5_funct_1(B_85,A_87)
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85)
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1119,plain,(
    ! [A_168,C_169,B_170] :
      ( ~ v1_xboole_0(k1_funct_1(A_168,C_169))
      | ~ r2_hidden(C_169,k1_relat_1(B_170))
      | ~ v5_funct_1(B_170,A_168)
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170)
      | ~ v1_funct_1(A_168)
      | ~ v1_relat_1(A_168) ) ),
    inference(resolution,[status(thm)],[c_352,c_4])).

tff(c_1127,plain,(
    ! [A_7,A_50,B_170] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_7,k1_relat_1(A_50)),k1_relat_1(B_170))
      | ~ v5_funct_1(B_170,A_50)
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50)
      | r1_tarski(A_7,k1_relat_1(A_50))
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1119])).

tff(c_2384,plain,(
    ! [A_261,A_262,B_263] :
      ( ~ r2_hidden('#skF_2'(A_261,k1_relat_1(A_262)),k1_relat_1(B_263))
      | ~ v5_funct_1(B_263,A_262)
      | ~ v1_funct_1(B_263)
      | ~ v1_relat_1(B_263)
      | r1_tarski(A_261,k1_relat_1(A_262))
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_1127])).

tff(c_2400,plain,(
    ! [B_264,A_265] :
      ( ~ v5_funct_1(B_264,A_265)
      | ~ v1_funct_1(B_264)
      | ~ v1_relat_1(B_264)
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265)
      | r1_tarski(k1_relat_1(B_264),k1_relat_1(A_265)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2384])).

tff(c_30,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2450,plain,
    ( ~ v5_funct_1('#skF_5','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2400,c_30])).

tff(c_2473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_2450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.82  
% 4.50/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.83  %$ v5_funct_1 > r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 4.50/1.83  
% 4.50/1.83  %Foreground sorts:
% 4.50/1.83  
% 4.50/1.83  
% 4.50/1.83  %Background operators:
% 4.50/1.83  
% 4.50/1.83  
% 4.50/1.83  %Foreground operators:
% 4.50/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.50/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.50/1.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.50/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.50/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.83  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 4.50/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.83  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.50/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.50/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.50/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.83  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.50/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.50/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.50/1.83  
% 4.50/1.84  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: (((v1_relat_1(B) & v1_funct_1(B)) & v5_funct_1(B, A)) => r1_tarski(k1_relat_1(B), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_1)).
% 4.50/1.84  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.50/1.84  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.50/1.84  tff(f_36, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.50/1.84  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 4.50/1.84  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 4.50/1.84  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 4.50/1.84  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.50/1.84  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.50/1.84  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.50/1.84  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.50/1.84  tff(c_32, plain, (v5_funct_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.50/1.84  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.50/1.84  tff(c_14, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.50/1.84  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.50/1.84  tff(c_73, plain, (![C_43, B_44, A_45]: (r2_hidden(C_43, B_44) | ~r2_hidden(C_43, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.50/1.84  tff(c_81, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48), B_49) | ~r1_tarski(A_48, B_49) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_6, c_73])).
% 4.50/1.84  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.50/1.84  tff(c_118, plain, (![B_52, A_53]: (~v1_xboole_0(B_52) | ~r1_tarski(A_53, B_52) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_81, c_4])).
% 4.50/1.84  tff(c_130, plain, (![A_12]: (~v1_xboole_0(A_12) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_118])).
% 4.50/1.84  tff(c_131, plain, (![A_12]: (~v1_xboole_0(A_12))), inference(splitLeft, [status(thm)], [c_130])).
% 4.50/1.84  tff(c_79, plain, (![A_3, B_44]: (r2_hidden('#skF_1'(A_3), B_44) | ~r1_tarski(A_3, B_44) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_73])).
% 4.50/1.84  tff(c_152, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59), B_60) | ~r1_tarski(A_59, B_60))), inference(negUnitSimplification, [status(thm)], [c_131, c_79])).
% 4.50/1.84  tff(c_48, plain, (![B_33, A_34]: (~r2_hidden(B_33, A_34) | ~r2_hidden(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.50/1.84  tff(c_51, plain, (![A_3]: (~r2_hidden(A_3, '#skF_1'(A_3)) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_48])).
% 4.50/1.84  tff(c_134, plain, (![A_3]: (~r2_hidden(A_3, '#skF_1'(A_3)))), inference(negUnitSimplification, [status(thm)], [c_131, c_51])).
% 4.50/1.84  tff(c_169, plain, (![A_61]: (~r1_tarski(A_61, '#skF_1'('#skF_1'(A_61))))), inference(resolution, [status(thm)], [c_152, c_134])).
% 4.50/1.84  tff(c_174, plain, $false, inference(resolution, [status(thm)], [c_14, c_169])).
% 4.50/1.84  tff(c_175, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_130])).
% 4.50/1.84  tff(c_102, plain, (![A_50, B_51]: (k1_funct_1(A_50, B_51)=k1_xboole_0 | r2_hidden(B_51, k1_relat_1(A_50)) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.50/1.84  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.50/1.84  tff(c_115, plain, (![A_7, A_50]: (r1_tarski(A_7, k1_relat_1(A_50)) | k1_funct_1(A_50, '#skF_2'(A_7, k1_relat_1(A_50)))=k1_xboole_0 | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(resolution, [status(thm)], [c_102, c_10])).
% 4.50/1.84  tff(c_352, plain, (![B_85, C_86, A_87]: (r2_hidden(k1_funct_1(B_85, C_86), k1_funct_1(A_87, C_86)) | ~r2_hidden(C_86, k1_relat_1(B_85)) | ~v5_funct_1(B_85, A_87) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.50/1.84  tff(c_1119, plain, (![A_168, C_169, B_170]: (~v1_xboole_0(k1_funct_1(A_168, C_169)) | ~r2_hidden(C_169, k1_relat_1(B_170)) | ~v5_funct_1(B_170, A_168) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170) | ~v1_funct_1(A_168) | ~v1_relat_1(A_168))), inference(resolution, [status(thm)], [c_352, c_4])).
% 4.50/1.84  tff(c_1127, plain, (![A_7, A_50, B_170]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden('#skF_2'(A_7, k1_relat_1(A_50)), k1_relat_1(B_170)) | ~v5_funct_1(B_170, A_50) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50) | r1_tarski(A_7, k1_relat_1(A_50)) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_115, c_1119])).
% 4.50/1.84  tff(c_2384, plain, (![A_261, A_262, B_263]: (~r2_hidden('#skF_2'(A_261, k1_relat_1(A_262)), k1_relat_1(B_263)) | ~v5_funct_1(B_263, A_262) | ~v1_funct_1(B_263) | ~v1_relat_1(B_263) | r1_tarski(A_261, k1_relat_1(A_262)) | ~v1_funct_1(A_262) | ~v1_relat_1(A_262))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_1127])).
% 4.50/1.84  tff(c_2400, plain, (![B_264, A_265]: (~v5_funct_1(B_264, A_265) | ~v1_funct_1(B_264) | ~v1_relat_1(B_264) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265) | r1_tarski(k1_relat_1(B_264), k1_relat_1(A_265)))), inference(resolution, [status(thm)], [c_12, c_2384])).
% 4.50/1.84  tff(c_30, plain, (~r1_tarski(k1_relat_1('#skF_5'), k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.50/1.84  tff(c_2450, plain, (~v5_funct_1('#skF_5', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2400, c_30])).
% 4.50/1.84  tff(c_2473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_2450])).
% 4.50/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.84  
% 4.50/1.84  Inference rules
% 4.50/1.84  ----------------------
% 4.50/1.84  #Ref     : 0
% 4.50/1.84  #Sup     : 554
% 4.50/1.84  #Fact    : 2
% 4.50/1.84  #Define  : 0
% 4.50/1.84  #Split   : 5
% 4.50/1.84  #Chain   : 0
% 4.50/1.84  #Close   : 0
% 4.50/1.84  
% 4.50/1.84  Ordering : KBO
% 4.50/1.84  
% 4.50/1.84  Simplification rules
% 4.50/1.84  ----------------------
% 4.50/1.84  #Subsume      : 282
% 4.50/1.84  #Demod        : 57
% 4.50/1.84  #Tautology    : 59
% 4.50/1.84  #SimpNegUnit  : 14
% 4.50/1.84  #BackRed      : 11
% 4.50/1.84  
% 4.50/1.84  #Partial instantiations: 0
% 4.50/1.84  #Strategies tried      : 1
% 4.50/1.84  
% 4.50/1.84  Timing (in seconds)
% 4.50/1.84  ----------------------
% 4.50/1.84  Preprocessing        : 0.28
% 4.50/1.84  Parsing              : 0.15
% 4.50/1.84  CNF conversion       : 0.02
% 4.50/1.84  Main loop            : 0.74
% 4.50/1.84  Inferencing          : 0.25
% 4.50/1.84  Reduction            : 0.17
% 4.50/1.84  Demodulation         : 0.11
% 4.50/1.84  BG Simplification    : 0.03
% 4.50/1.84  Subsumption          : 0.24
% 4.50/1.84  Abstraction          : 0.03
% 4.50/1.84  MUC search           : 0.00
% 4.50/1.84  Cooper               : 0.00
% 4.50/1.84  Total                : 1.05
% 4.50/1.84  Index Insertion      : 0.00
% 4.50/1.84  Index Deletion       : 0.00
% 4.50/1.84  Index Matching       : 0.00
% 4.50/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
