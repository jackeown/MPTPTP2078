%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 162 expanded)
%              Number of leaves         :   29 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 314 expanded)
%              Number of equality atoms :   48 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_476,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ r1_tarski(A_85,B_84)
      | ~ v1_zfmisc_1(B_84)
      | v1_xboole_0(B_84)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_732,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(A_96,B_97) = A_96
      | ~ v1_zfmisc_1(A_96)
      | v1_xboole_0(A_96)
      | v1_xboole_0(k3_xboole_0(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_16,c_476])).

tff(c_38,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_738,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_732,c_38])).

tff(c_757,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_738])).

tff(c_758,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_757])).

tff(c_124,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(A_54,B_55)
      | k3_xboole_0(A_54,B_55) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_542,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = A_87
      | k3_xboole_0(A_87,B_88) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_124,c_20])).

tff(c_204,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | k4_xboole_0(A_60,B_61) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_212,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_204,c_36])).

tff(c_560,plain,
    ( k1_xboole_0 != '#skF_3'
    | k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_212])).

tff(c_637,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_560])).

tff(c_762,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_637])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_71,plain,(
    ! [A_13,B_14] : k4_xboole_0(k4_xboole_0(A_13,B_14),A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_63])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1015,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ v1_zfmisc_1(B_102)
      | v1_xboole_0(B_102)
      | v1_xboole_0(A_103)
      | k4_xboole_0(A_103,B_102) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_476])).

tff(c_1017,plain,(
    ! [A_103] :
      ( A_103 = '#skF_3'
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_103)
      | k4_xboole_0(A_103,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_1015])).

tff(c_1021,plain,(
    ! [A_104] :
      ( A_104 = '#skF_3'
      | v1_xboole_0(A_104)
      | k4_xboole_0(A_104,'#skF_3') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1017])).

tff(c_52,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_2'(A_38),A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [A_38] :
      ( ~ v1_xboole_0(A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_1033,plain,(
    ! [A_105] :
      ( k1_xboole_0 = A_105
      | A_105 = '#skF_3'
      | k4_xboole_0(A_105,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1021,c_56])).

tff(c_1098,plain,(
    ! [B_108] :
      ( k4_xboole_0('#skF_3',B_108) = k1_xboole_0
      | k4_xboole_0('#skF_3',B_108) = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1033])).

tff(c_1156,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_212])).

tff(c_233,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(A_66,B_67)
      | k4_xboole_0(A_66,B_67) != A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_241,plain,(
    ! [A_66,B_67] :
      ( k3_xboole_0(A_66,B_67) = k1_xboole_0
      | k4_xboole_0(A_66,B_67) != A_66 ) ),
    inference(resolution,[status(thm)],[c_233,c_6])).

tff(c_1182,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_241])).

tff(c_1209,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_1182])).

tff(c_1211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_762,c_1209])).

tff(c_1213,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_1214,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_38])).

tff(c_1212,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_560])).

tff(c_1237,plain,(
    ! [A_109,B_110] :
      ( k3_xboole_0(A_109,B_110) = A_109
      | ~ v1_zfmisc_1(A_109)
      | v1_xboole_0(A_109)
      | v1_xboole_0(k3_xboole_0(A_109,B_110)) ) ),
    inference(resolution,[status(thm)],[c_16,c_476])).

tff(c_1243,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_1237])).

tff(c_1261,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1213,c_1243])).

tff(c_1262,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1212,c_1261])).

tff(c_1266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1214,c_1262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.49  
% 2.97/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.97/1.50  
% 2.97/1.50  %Foreground sorts:
% 2.97/1.50  
% 2.97/1.50  
% 2.97/1.50  %Background operators:
% 2.97/1.50  
% 2.97/1.50  
% 2.97/1.50  %Foreground operators:
% 2.97/1.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.97/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.97/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.50  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.97/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.97/1.50  
% 2.97/1.51  tff(f_90, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.97/1.51  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.97/1.51  tff(f_78, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.97/1.51  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.97/1.51  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.97/1.51  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.97/1.51  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.97/1.51  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.97/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.97/1.51  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.51  tff(c_40, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.51  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.97/1.51  tff(c_476, plain, (![B_84, A_85]: (B_84=A_85 | ~r1_tarski(A_85, B_84) | ~v1_zfmisc_1(B_84) | v1_xboole_0(B_84) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.97/1.51  tff(c_732, plain, (![A_96, B_97]: (k3_xboole_0(A_96, B_97)=A_96 | ~v1_zfmisc_1(A_96) | v1_xboole_0(A_96) | v1_xboole_0(k3_xboole_0(A_96, B_97)))), inference(resolution, [status(thm)], [c_16, c_476])).
% 2.97/1.51  tff(c_38, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.51  tff(c_738, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_732, c_38])).
% 2.97/1.51  tff(c_757, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_738])).
% 2.97/1.51  tff(c_758, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_42, c_757])).
% 2.97/1.51  tff(c_124, plain, (![A_54, B_55]: (r1_xboole_0(A_54, B_55) | k3_xboole_0(A_54, B_55)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.51  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.51  tff(c_542, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=A_87 | k3_xboole_0(A_87, B_88)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_124, c_20])).
% 2.97/1.51  tff(c_204, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | k4_xboole_0(A_60, B_61)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.51  tff(c_36, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.97/1.51  tff(c_212, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_204, c_36])).
% 2.97/1.51  tff(c_560, plain, (k1_xboole_0!='#skF_3' | k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_542, c_212])).
% 2.97/1.51  tff(c_637, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_560])).
% 2.97/1.51  tff(c_762, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_758, c_637])).
% 2.97/1.51  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.97/1.51  tff(c_63, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.51  tff(c_71, plain, (![A_13, B_14]: (k4_xboole_0(k4_xboole_0(A_13, B_14), A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_63])).
% 2.97/1.51  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.97/1.51  tff(c_1015, plain, (![B_102, A_103]: (B_102=A_103 | ~v1_zfmisc_1(B_102) | v1_xboole_0(B_102) | v1_xboole_0(A_103) | k4_xboole_0(A_103, B_102)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_476])).
% 2.97/1.51  tff(c_1017, plain, (![A_103]: (A_103='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(A_103) | k4_xboole_0(A_103, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1015])).
% 2.97/1.51  tff(c_1021, plain, (![A_104]: (A_104='#skF_3' | v1_xboole_0(A_104) | k4_xboole_0(A_104, '#skF_3')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_42, c_1017])).
% 2.97/1.51  tff(c_52, plain, (![A_38]: (r2_hidden('#skF_2'(A_38), A_38) | k1_xboole_0=A_38)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.97/1.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.51  tff(c_56, plain, (![A_38]: (~v1_xboole_0(A_38) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_52, c_2])).
% 2.97/1.51  tff(c_1033, plain, (![A_105]: (k1_xboole_0=A_105 | A_105='#skF_3' | k4_xboole_0(A_105, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1021, c_56])).
% 2.97/1.51  tff(c_1098, plain, (![B_108]: (k4_xboole_0('#skF_3', B_108)=k1_xboole_0 | k4_xboole_0('#skF_3', B_108)='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_71, c_1033])).
% 2.97/1.51  tff(c_1156, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1098, c_212])).
% 2.97/1.51  tff(c_233, plain, (![A_66, B_67]: (r1_xboole_0(A_66, B_67) | k4_xboole_0(A_66, B_67)!=A_66)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.97/1.51  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.51  tff(c_241, plain, (![A_66, B_67]: (k3_xboole_0(A_66, B_67)=k1_xboole_0 | k4_xboole_0(A_66, B_67)!=A_66)), inference(resolution, [status(thm)], [c_233, c_6])).
% 2.97/1.51  tff(c_1182, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1156, c_241])).
% 2.97/1.51  tff(c_1209, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_758, c_1182])).
% 2.97/1.51  tff(c_1211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_762, c_1209])).
% 2.97/1.51  tff(c_1213, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_560])).
% 2.97/1.51  tff(c_1214, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_38])).
% 2.97/1.51  tff(c_1212, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_560])).
% 2.97/1.51  tff(c_1237, plain, (![A_109, B_110]: (k3_xboole_0(A_109, B_110)=A_109 | ~v1_zfmisc_1(A_109) | v1_xboole_0(A_109) | v1_xboole_0(k3_xboole_0(A_109, B_110)))), inference(resolution, [status(thm)], [c_16, c_476])).
% 2.97/1.51  tff(c_1243, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1213, c_1237])).
% 2.97/1.51  tff(c_1261, plain, (k1_xboole_0='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1213, c_1243])).
% 2.97/1.51  tff(c_1262, plain, (v1_xboole_0(k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_42, c_1212, c_1261])).
% 2.97/1.51  tff(c_1266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1214, c_1262])).
% 2.97/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.51  
% 2.97/1.51  Inference rules
% 2.97/1.51  ----------------------
% 2.97/1.51  #Ref     : 0
% 2.97/1.51  #Sup     : 318
% 2.97/1.51  #Fact    : 1
% 2.97/1.51  #Define  : 0
% 2.97/1.51  #Split   : 1
% 2.97/1.51  #Chain   : 0
% 2.97/1.51  #Close   : 0
% 2.97/1.51  
% 2.97/1.51  Ordering : KBO
% 2.97/1.51  
% 2.97/1.51  Simplification rules
% 2.97/1.51  ----------------------
% 2.97/1.51  #Subsume      : 33
% 2.97/1.51  #Demod        : 181
% 2.97/1.51  #Tautology    : 212
% 2.97/1.51  #SimpNegUnit  : 22
% 2.97/1.51  #BackRed      : 5
% 2.97/1.51  
% 2.97/1.51  #Partial instantiations: 0
% 2.97/1.51  #Strategies tried      : 1
% 2.97/1.51  
% 2.97/1.51  Timing (in seconds)
% 2.97/1.51  ----------------------
% 2.97/1.51  Preprocessing        : 0.30
% 3.09/1.51  Parsing              : 0.16
% 3.09/1.51  CNF conversion       : 0.02
% 3.09/1.52  Main loop            : 0.44
% 3.09/1.52  Inferencing          : 0.17
% 3.09/1.52  Reduction            : 0.14
% 3.09/1.52  Demodulation         : 0.10
% 3.09/1.52  BG Simplification    : 0.02
% 3.09/1.52  Subsumption          : 0.06
% 3.09/1.52  Abstraction          : 0.03
% 3.09/1.52  MUC search           : 0.00
% 3.09/1.52  Cooper               : 0.00
% 3.09/1.52  Total                : 0.77
% 3.09/1.52  Index Insertion      : 0.00
% 3.09/1.52  Index Deletion       : 0.00
% 3.09/1.52  Index Matching       : 0.00
% 3.09/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
