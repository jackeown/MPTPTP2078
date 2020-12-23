%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:04 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 148 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  106 ( 405 expanded)
%              Number of equality atoms :   64 ( 210 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_86,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_67,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(c_146,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_1'(A_56,B_57),B_57)
      | r2_hidden('#skF_2'(A_56,B_57),A_56)
      | B_57 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    ! [B_48,A_49] :
      ( ~ r2_hidden(B_48,A_49)
      | k4_xboole_0(A_49,k1_tarski(B_48)) != A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [B_48] : ~ r2_hidden(B_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_125])).

tff(c_159,plain,(
    ! [B_57] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_57),B_57)
      | k1_xboole_0 = B_57 ) ),
    inference(resolution,[status(thm)],[c_146,c_134])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_10,B_11] : v1_funct_1('#skF_3'(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_10,B_11] : k1_relat_1('#skF_3'(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_10,B_11] : v1_relat_1('#skF_3'(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ! [A_17] : v1_funct_1('#skF_4'(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    ! [A_17] : k1_relat_1('#skF_4'(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_17] : v1_relat_1('#skF_4'(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_77,plain,(
    ! [C_40,B_41] :
      ( C_40 = B_41
      | k1_relat_1(C_40) != '#skF_5'
      | k1_relat_1(B_41) != '#skF_5'
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_81,plain,(
    ! [B_41,A_17] :
      ( B_41 = '#skF_4'(A_17)
      | k1_relat_1('#skF_4'(A_17)) != '#skF_5'
      | k1_relat_1(B_41) != '#skF_5'
      | ~ v1_funct_1('#skF_4'(A_17))
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_168,plain,(
    ! [B_59,A_60] :
      ( B_59 = '#skF_4'(A_60)
      | A_60 != '#skF_5'
      | k1_relat_1(B_59) != '#skF_5'
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_81])).

tff(c_170,plain,(
    ! [A_60,A_10,B_11] :
      ( '#skF_4'(A_60) = '#skF_3'(A_10,B_11)
      | A_60 != '#skF_5'
      | k1_relat_1('#skF_3'(A_10,B_11)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_10,B_11)) ) ),
    inference(resolution,[status(thm)],[c_26,c_168])).

tff(c_237,plain,(
    ! [A_65,A_66,B_67] :
      ( '#skF_4'(A_65) = '#skF_3'(A_66,B_67)
      | A_65 != '#skF_5'
      | A_66 != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_170])).

tff(c_20,plain,(
    ! [A_10,B_11,D_16] :
      ( k1_funct_1('#skF_3'(A_10,B_11),D_16) = B_11
      | ~ r2_hidden(D_16,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_307,plain,(
    ! [A_72,D_73,B_74,A_75] :
      ( k1_funct_1('#skF_4'(A_72),D_73) = B_74
      | ~ r2_hidden(D_73,A_75)
      | A_72 != '#skF_5'
      | A_75 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_20])).

tff(c_796,plain,(
    ! [A_72,B_57] :
      ( k1_funct_1('#skF_4'(A_72),'#skF_1'(k1_xboole_0,B_57)) = '#skF_5'
      | A_72 != '#skF_5'
      | B_57 != '#skF_5'
      | k1_xboole_0 = B_57 ) ),
    inference(resolution,[status(thm)],[c_159,c_307])).

tff(c_583,plain,(
    ! [A_92,B_93] :
      ( k1_funct_1('#skF_4'(A_92),'#skF_1'(k1_xboole_0,B_93)) = k1_xboole_0
      | A_92 != '#skF_5'
      | B_93 != '#skF_5'
      | k1_xboole_0 = B_93 ) ),
    inference(resolution,[status(thm)],[c_159,c_307])).

tff(c_28,plain,(
    ! [A_17,C_22] :
      ( k1_funct_1('#skF_4'(A_17),C_22) = np__1
      | ~ r2_hidden(C_22,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_586,plain,(
    ! [B_93,A_92] :
      ( np__1 = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k1_xboole_0,B_93),A_92)
      | A_92 != '#skF_5'
      | B_93 != '#skF_5'
      | k1_xboole_0 = B_93 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_28])).

tff(c_750,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_586])).

tff(c_756,plain,(
    ! [A_702,C_703] :
      ( k1_funct_1('#skF_4'(A_702),C_703) = k1_xboole_0
      | ~ r2_hidden(C_703,A_702) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_750,c_28])).

tff(c_799,plain,(
    ! [B_57,A_72] :
      ( k1_xboole_0 = '#skF_5'
      | ~ r2_hidden('#skF_1'(k1_xboole_0,B_57),A_72)
      | A_72 != '#skF_5'
      | B_57 != '#skF_5'
      | k1_xboole_0 = B_57 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_756])).

tff(c_851,plain,(
    ! [B_722,A_723] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_722),A_723)
      | A_723 != '#skF_5'
      | B_722 != '#skF_5'
      | k1_xboole_0 = B_722 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_799])).

tff(c_865,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_159,c_851])).

tff(c_875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_36])).

tff(c_879,plain,(
    ! [B_760,A_761] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_760),A_761)
      | A_761 != '#skF_5'
      | B_760 != '#skF_5'
      | k1_xboole_0 = B_760 ) ),
    inference(splitRight,[status(thm)],[c_586])).

tff(c_893,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_159,c_879])).

tff(c_902,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 2.72/1.40  
% 2.72/1.40  %Foreground sorts:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Background operators:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Foreground operators:
% 2.72/1.40  tff(np__1, type, np__1: $i).
% 2.72/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.72/1.40  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.72/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.72/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.40  
% 2.72/1.41  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.72/1.41  tff(f_34, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.72/1.41  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.72/1.41  tff(f_86, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 2.72/1.41  tff(f_55, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 2.72/1.41  tff(f_67, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.72/1.41  tff(c_146, plain, (![A_56, B_57]: (r2_hidden('#skF_1'(A_56, B_57), B_57) | r2_hidden('#skF_2'(A_56, B_57), A_56) | B_57=A_56)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.72/1.41  tff(c_10, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.72/1.41  tff(c_125, plain, (![B_48, A_49]: (~r2_hidden(B_48, A_49) | k4_xboole_0(A_49, k1_tarski(B_48))!=A_49)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.41  tff(c_134, plain, (![B_48]: (~r2_hidden(B_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_125])).
% 2.72/1.41  tff(c_159, plain, (![B_57]: (r2_hidden('#skF_1'(k1_xboole_0, B_57), B_57) | k1_xboole_0=B_57)), inference(resolution, [status(thm)], [c_146, c_134])).
% 2.72/1.41  tff(c_36, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.72/1.41  tff(c_24, plain, (![A_10, B_11]: (v1_funct_1('#skF_3'(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.41  tff(c_22, plain, (![A_10, B_11]: (k1_relat_1('#skF_3'(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.41  tff(c_26, plain, (![A_10, B_11]: (v1_relat_1('#skF_3'(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.41  tff(c_32, plain, (![A_17]: (v1_funct_1('#skF_4'(A_17)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_30, plain, (![A_17]: (k1_relat_1('#skF_4'(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_34, plain, (![A_17]: (v1_relat_1('#skF_4'(A_17)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_77, plain, (![C_40, B_41]: (C_40=B_41 | k1_relat_1(C_40)!='#skF_5' | k1_relat_1(B_41)!='#skF_5' | ~v1_funct_1(C_40) | ~v1_relat_1(C_40) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.72/1.41  tff(c_81, plain, (![B_41, A_17]: (B_41='#skF_4'(A_17) | k1_relat_1('#skF_4'(A_17))!='#skF_5' | k1_relat_1(B_41)!='#skF_5' | ~v1_funct_1('#skF_4'(A_17)) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(resolution, [status(thm)], [c_34, c_77])).
% 2.72/1.41  tff(c_168, plain, (![B_59, A_60]: (B_59='#skF_4'(A_60) | A_60!='#skF_5' | k1_relat_1(B_59)!='#skF_5' | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_81])).
% 2.72/1.41  tff(c_170, plain, (![A_60, A_10, B_11]: ('#skF_4'(A_60)='#skF_3'(A_10, B_11) | A_60!='#skF_5' | k1_relat_1('#skF_3'(A_10, B_11))!='#skF_5' | ~v1_funct_1('#skF_3'(A_10, B_11)))), inference(resolution, [status(thm)], [c_26, c_168])).
% 2.72/1.41  tff(c_237, plain, (![A_65, A_66, B_67]: ('#skF_4'(A_65)='#skF_3'(A_66, B_67) | A_65!='#skF_5' | A_66!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_170])).
% 2.72/1.41  tff(c_20, plain, (![A_10, B_11, D_16]: (k1_funct_1('#skF_3'(A_10, B_11), D_16)=B_11 | ~r2_hidden(D_16, A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.41  tff(c_307, plain, (![A_72, D_73, B_74, A_75]: (k1_funct_1('#skF_4'(A_72), D_73)=B_74 | ~r2_hidden(D_73, A_75) | A_72!='#skF_5' | A_75!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_237, c_20])).
% 2.72/1.41  tff(c_796, plain, (![A_72, B_57]: (k1_funct_1('#skF_4'(A_72), '#skF_1'(k1_xboole_0, B_57))='#skF_5' | A_72!='#skF_5' | B_57!='#skF_5' | k1_xboole_0=B_57)), inference(resolution, [status(thm)], [c_159, c_307])).
% 2.72/1.41  tff(c_583, plain, (![A_92, B_93]: (k1_funct_1('#skF_4'(A_92), '#skF_1'(k1_xboole_0, B_93))=k1_xboole_0 | A_92!='#skF_5' | B_93!='#skF_5' | k1_xboole_0=B_93)), inference(resolution, [status(thm)], [c_159, c_307])).
% 2.72/1.41  tff(c_28, plain, (![A_17, C_22]: (k1_funct_1('#skF_4'(A_17), C_22)=np__1 | ~r2_hidden(C_22, A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.72/1.41  tff(c_586, plain, (![B_93, A_92]: (np__1=k1_xboole_0 | ~r2_hidden('#skF_1'(k1_xboole_0, B_93), A_92) | A_92!='#skF_5' | B_93!='#skF_5' | k1_xboole_0=B_93)), inference(superposition, [status(thm), theory('equality')], [c_583, c_28])).
% 2.72/1.41  tff(c_750, plain, (np__1=k1_xboole_0), inference(splitLeft, [status(thm)], [c_586])).
% 2.72/1.41  tff(c_756, plain, (![A_702, C_703]: (k1_funct_1('#skF_4'(A_702), C_703)=k1_xboole_0 | ~r2_hidden(C_703, A_702))), inference(demodulation, [status(thm), theory('equality')], [c_750, c_28])).
% 2.72/1.41  tff(c_799, plain, (![B_57, A_72]: (k1_xboole_0='#skF_5' | ~r2_hidden('#skF_1'(k1_xboole_0, B_57), A_72) | A_72!='#skF_5' | B_57!='#skF_5' | k1_xboole_0=B_57)), inference(superposition, [status(thm), theory('equality')], [c_796, c_756])).
% 2.72/1.41  tff(c_851, plain, (![B_722, A_723]: (~r2_hidden('#skF_1'(k1_xboole_0, B_722), A_723) | A_723!='#skF_5' | B_722!='#skF_5' | k1_xboole_0=B_722)), inference(negUnitSimplification, [status(thm)], [c_36, c_799])).
% 2.72/1.41  tff(c_865, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_159, c_851])).
% 2.72/1.41  tff(c_875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_865, c_36])).
% 2.72/1.41  tff(c_879, plain, (![B_760, A_761]: (~r2_hidden('#skF_1'(k1_xboole_0, B_760), A_761) | A_761!='#skF_5' | B_760!='#skF_5' | k1_xboole_0=B_760)), inference(splitRight, [status(thm)], [c_586])).
% 2.72/1.41  tff(c_893, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_159, c_879])).
% 2.72/1.41  tff(c_902, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_893, c_36])).
% 2.72/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  Inference rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Ref     : 1
% 2.72/1.41  #Sup     : 205
% 2.72/1.41  #Fact    : 0
% 2.72/1.41  #Define  : 0
% 2.72/1.41  #Split   : 1
% 2.72/1.41  #Chain   : 0
% 2.72/1.41  #Close   : 0
% 2.72/1.41  
% 2.72/1.41  Ordering : KBO
% 2.72/1.41  
% 2.72/1.41  Simplification rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Subsume      : 61
% 2.72/1.41  #Demod        : 55
% 2.72/1.41  #Tautology    : 46
% 2.72/1.41  #SimpNegUnit  : 3
% 2.72/1.41  #BackRed      : 12
% 2.72/1.41  
% 2.72/1.41  #Partial instantiations: 468
% 2.72/1.41  #Strategies tried      : 1
% 2.72/1.41  
% 2.72/1.41  Timing (in seconds)
% 2.72/1.41  ----------------------
% 2.72/1.41  Preprocessing        : 0.29
% 2.72/1.41  Parsing              : 0.16
% 2.72/1.41  CNF conversion       : 0.02
% 2.72/1.41  Main loop            : 0.36
% 2.72/1.41  Inferencing          : 0.15
% 2.72/1.41  Reduction            : 0.09
% 2.72/1.41  Demodulation         : 0.06
% 2.72/1.41  BG Simplification    : 0.02
% 2.72/1.41  Subsumption          : 0.08
% 2.72/1.42  Abstraction          : 0.02
% 2.72/1.42  MUC search           : 0.00
% 2.72/1.42  Cooper               : 0.00
% 2.72/1.42  Total                : 0.68
% 2.72/1.42  Index Insertion      : 0.00
% 2.72/1.42  Index Deletion       : 0.00
% 2.72/1.42  Index Matching       : 0.00
% 2.72/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
