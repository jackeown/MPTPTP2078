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
% DateTime   : Thu Dec  3 09:58:37 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 244 expanded)
%              Number of leaves         :   38 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 402 expanded)
%              Number of equality atoms :   11 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_72,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_346,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),A_90)
      | r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_383,plain,(
    ! [A_95,B_96,B_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | r1_tarski(k3_xboole_0(A_95,B_96),B_97) ) ),
    inference(resolution,[status(thm)],[c_346,c_10])).

tff(c_24,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_163,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_175,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_163])).

tff(c_404,plain,(
    ! [A_101,B_102] :
      ( k3_xboole_0(A_101,B_102) = k1_xboole_0
      | ~ r1_xboole_0(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_383,c_175])).

tff(c_408,plain,(
    ! [A_27] : k3_xboole_0(A_27,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_404])).

tff(c_28,plain,(
    ! [A_24] : k4_xboole_0(A_24,k1_xboole_0) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_102,plain,(
    ! [A_62,B_63] : k2_xboole_0(k3_xboole_0(A_62,B_63),k4_xboole_0(A_62,B_63)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_111,plain,(
    ! [A_24] : k2_xboole_0(k3_xboole_0(A_24,k1_xboole_0),A_24) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_102])).

tff(c_409,plain,(
    ! [A_24] : k2_xboole_0(k1_xboole_0,A_24) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_111])).

tff(c_566,plain,(
    ! [A_116,B_117,C_118] : r1_tarski(k2_xboole_0(k3_xboole_0(A_116,B_117),k3_xboole_0(A_116,C_118)),k2_xboole_0(B_117,C_118)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_574,plain,(
    ! [A_116,A_24] : r1_tarski(k2_xboole_0(k3_xboole_0(A_116,k1_xboole_0),k3_xboole_0(A_116,A_24)),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_566])).

tff(c_621,plain,(
    ! [A_122,A_123] : r1_tarski(k3_xboole_0(A_122,A_123),A_123) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_408,c_574])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_128,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(A_37)
      | ~ v1_relat_1(B_38)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_44,c_124])).

tff(c_640,plain,(
    ! [A_122,A_123] :
      ( v1_relat_1(k3_xboole_0(A_122,A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_621,c_128])).

tff(c_592,plain,(
    ! [A_116,A_24] : r1_tarski(k3_xboole_0(A_116,A_24),A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_408,c_574])).

tff(c_48,plain,(
    ! [A_42,B_44] :
      ( r1_tarski(k3_relat_1(A_42),k3_relat_1(B_44))
      | ~ r1_tarski(A_42,B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_20,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_596,plain,(
    ! [A_119,B_120,C_121] :
      ( r1_tarski(A_119,k3_xboole_0(B_120,C_121))
      | ~ r1_tarski(A_119,C_121)
      | ~ r1_tarski(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k3_relat_1('#skF_3'),k3_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_620,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_596,c_50])).

tff(c_825,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_620])).

tff(c_858,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_825])).

tff(c_861,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20,c_858])).

tff(c_864,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_640,c_861])).

tff(c_874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_864])).

tff(c_875,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_620])).

tff(c_898,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_875])).

tff(c_901,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_592,c_898])).

tff(c_904,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_640,c_901])).

tff(c_914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:17:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.79/1.43  
% 2.79/1.43  %Foreground sorts:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Background operators:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Foreground operators:
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.43  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.79/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.79/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.79/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.79/1.43  
% 2.79/1.45  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.79/1.45  tff(f_72, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.79/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.79/1.45  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.79/1.45  tff(f_64, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.79/1.45  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.45  tff(f_68, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.79/1.45  tff(f_70, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.79/1.45  tff(f_66, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.79/1.45  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.45  tff(f_91, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.45  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.79/1.45  tff(f_56, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.79/1.45  tff(f_62, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.79/1.45  tff(c_52, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.45  tff(c_32, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.45  tff(c_346, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), A_90) | r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.45  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.45  tff(c_383, plain, (![A_95, B_96, B_97]: (~r1_xboole_0(A_95, B_96) | r1_tarski(k3_xboole_0(A_95, B_96), B_97))), inference(resolution, [status(thm)], [c_346, c_10])).
% 2.79/1.45  tff(c_24, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.79/1.45  tff(c_163, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.79/1.45  tff(c_175, plain, (![A_20]: (k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_163])).
% 2.79/1.45  tff(c_404, plain, (![A_101, B_102]: (k3_xboole_0(A_101, B_102)=k1_xboole_0 | ~r1_xboole_0(A_101, B_102))), inference(resolution, [status(thm)], [c_383, c_175])).
% 2.79/1.45  tff(c_408, plain, (![A_27]: (k3_xboole_0(A_27, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_404])).
% 2.79/1.45  tff(c_28, plain, (![A_24]: (k4_xboole_0(A_24, k1_xboole_0)=A_24)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.45  tff(c_102, plain, (![A_62, B_63]: (k2_xboole_0(k3_xboole_0(A_62, B_63), k4_xboole_0(A_62, B_63))=A_62)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.79/1.45  tff(c_111, plain, (![A_24]: (k2_xboole_0(k3_xboole_0(A_24, k1_xboole_0), A_24)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_28, c_102])).
% 2.79/1.45  tff(c_409, plain, (![A_24]: (k2_xboole_0(k1_xboole_0, A_24)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_408, c_111])).
% 2.79/1.45  tff(c_566, plain, (![A_116, B_117, C_118]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_116, B_117), k3_xboole_0(A_116, C_118)), k2_xboole_0(B_117, C_118)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.45  tff(c_574, plain, (![A_116, A_24]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_116, k1_xboole_0), k3_xboole_0(A_116, A_24)), A_24))), inference(superposition, [status(thm), theory('equality')], [c_409, c_566])).
% 2.79/1.45  tff(c_621, plain, (![A_122, A_123]: (r1_tarski(k3_xboole_0(A_122, A_123), A_123))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_408, c_574])).
% 2.79/1.45  tff(c_44, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.79/1.45  tff(c_124, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.45  tff(c_128, plain, (![A_37, B_38]: (v1_relat_1(A_37) | ~v1_relat_1(B_38) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_44, c_124])).
% 2.79/1.45  tff(c_640, plain, (![A_122, A_123]: (v1_relat_1(k3_xboole_0(A_122, A_123)) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_621, c_128])).
% 2.79/1.45  tff(c_592, plain, (![A_116, A_24]: (r1_tarski(k3_xboole_0(A_116, A_24), A_24))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_408, c_574])).
% 2.79/1.45  tff(c_48, plain, (![A_42, B_44]: (r1_tarski(k3_relat_1(A_42), k3_relat_1(B_44)) | ~r1_tarski(A_42, B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.79/1.45  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.45  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.79/1.45  tff(c_596, plain, (![A_119, B_120, C_121]: (r1_tarski(A_119, k3_xboole_0(B_120, C_121)) | ~r1_tarski(A_119, C_121) | ~r1_tarski(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.79/1.45  tff(c_50, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k3_relat_1('#skF_3'), k3_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.79/1.45  tff(c_620, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_596, c_50])).
% 2.79/1.45  tff(c_825, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_620])).
% 2.79/1.45  tff(c_858, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_825])).
% 2.79/1.45  tff(c_861, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_20, c_858])).
% 2.79/1.45  tff(c_864, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_640, c_861])).
% 2.79/1.45  tff(c_874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_864])).
% 2.79/1.45  tff(c_875, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_620])).
% 2.79/1.45  tff(c_898, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_875])).
% 2.79/1.45  tff(c_901, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_592, c_898])).
% 2.79/1.45  tff(c_904, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_640, c_901])).
% 2.79/1.45  tff(c_914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_904])).
% 2.79/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  Inference rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Ref     : 0
% 2.79/1.45  #Sup     : 199
% 2.79/1.45  #Fact    : 0
% 2.79/1.45  #Define  : 0
% 2.79/1.45  #Split   : 4
% 2.79/1.45  #Chain   : 0
% 2.79/1.45  #Close   : 0
% 2.79/1.45  
% 2.79/1.45  Ordering : KBO
% 2.79/1.45  
% 2.79/1.45  Simplification rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Subsume      : 21
% 2.79/1.45  #Demod        : 105
% 2.79/1.45  #Tautology    : 120
% 2.79/1.45  #SimpNegUnit  : 12
% 2.79/1.45  #BackRed      : 8
% 2.79/1.45  
% 2.79/1.45  #Partial instantiations: 0
% 2.79/1.45  #Strategies tried      : 1
% 2.79/1.45  
% 2.79/1.45  Timing (in seconds)
% 2.79/1.45  ----------------------
% 2.79/1.45  Preprocessing        : 0.34
% 2.79/1.45  Parsing              : 0.19
% 2.79/1.45  CNF conversion       : 0.02
% 2.79/1.45  Main loop            : 0.32
% 2.79/1.45  Inferencing          : 0.12
% 2.79/1.45  Reduction            : 0.11
% 2.79/1.45  Demodulation         : 0.08
% 2.79/1.45  BG Simplification    : 0.02
% 2.79/1.45  Subsumption          : 0.05
% 2.79/1.45  Abstraction          : 0.02
% 2.79/1.45  MUC search           : 0.00
% 2.79/1.45  Cooper               : 0.00
% 2.79/1.45  Total                : 0.70
% 2.79/1.45  Index Insertion      : 0.00
% 2.79/1.45  Index Deletion       : 0.00
% 2.79/1.45  Index Matching       : 0.00
% 2.79/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
