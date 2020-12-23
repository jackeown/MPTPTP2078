%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:24 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 141 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 270 expanded)
%              Number of equality atoms :   35 (  76 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_32,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_16,plain,(
    ! [A_12] :
      ( k2_relat_1(A_12) = k1_xboole_0
      | k1_relat_1(A_12) != k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_67,plain,
    ( k2_relat_1('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_16])).

tff(c_68,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_123,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_137,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_123])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k7_relat_1(B_11,A_10) = B_11
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_140,plain,
    ( k7_relat_1('#skF_5','#skF_4') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_12])).

tff(c_143,plain,(
    k7_relat_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_140])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_147,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_18])).

tff(c_151,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_147])).

tff(c_288,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_312,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_288])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_115,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_154,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70),B_71)
      | ~ r1_tarski(A_70,B_71)
      | k1_xboole_0 = A_70 ) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_167,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1('#skF_2'(A_72),B_73)
      | ~ r1_tarski(A_72,B_73)
      | k1_xboole_0 = A_72 ) ),
    inference(resolution,[status(thm)],[c_154,c_10])).

tff(c_48,plain,(
    ! [D_46] :
      ( ~ r2_hidden(D_46,k1_relset_1('#skF_4','#skF_3','#skF_5'))
      | ~ m1_subset_1(D_46,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_53,plain,
    ( ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_93,plain,(
    ~ m1_subset_1('#skF_2'(k1_relset_1('#skF_4','#skF_3','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_185,plain,
    ( ~ r1_tarski(k1_relset_1('#skF_4','#skF_3','#skF_5'),'#skF_4')
    | k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_93])).

tff(c_287,plain,(
    ~ r1_tarski(k1_relset_1('#skF_4','#skF_3','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_313,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_287])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_313])).

tff(c_321,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_331,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_350,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_331])).

tff(c_356,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_350])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_356])).

tff(c_359,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_599,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_618,plain,(
    k1_relset_1('#skF_4','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_599])).

tff(c_624,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_618])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_624])).

tff(c_627,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_735,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_relset_1(A_156,B_157,C_158) = k2_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_746,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_735])).

tff(c_750,plain,(
    k2_relset_1('#skF_4','#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_746])).

tff(c_752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 15:55:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.43  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.82/1.43  
% 2.82/1.43  %Foreground sorts:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Background operators:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Foreground operators:
% 2.82/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.82/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.43  
% 2.82/1.44  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.82/1.44  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.82/1.44  tff(f_56, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.82/1.44  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.82/1.44  tff(f_50, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.82/1.44  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.82/1.44  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.82/1.44  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.82/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.82/1.44  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.82/1.44  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.82/1.44  tff(c_32, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.82/1.44  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.82/1.44  tff(c_54, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.82/1.44  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.82/1.44  tff(c_16, plain, (![A_12]: (k2_relat_1(A_12)=k1_xboole_0 | k1_relat_1(A_12)!=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.82/1.44  tff(c_67, plain, (k2_relat_1('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_16])).
% 2.82/1.44  tff(c_68, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_67])).
% 2.82/1.44  tff(c_123, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.82/1.44  tff(c_137, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_123])).
% 2.82/1.44  tff(c_12, plain, (![B_11, A_10]: (k7_relat_1(B_11, A_10)=B_11 | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.82/1.44  tff(c_140, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_137, c_12])).
% 2.82/1.44  tff(c_143, plain, (k7_relat_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_140])).
% 2.82/1.44  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.44  tff(c_147, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_143, c_18])).
% 2.82/1.44  tff(c_151, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_147])).
% 2.82/1.44  tff(c_288, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.44  tff(c_312, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_288])).
% 2.82/1.44  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.82/1.44  tff(c_115, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.82/1.44  tff(c_154, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70), B_71) | ~r1_tarski(A_70, B_71) | k1_xboole_0=A_70)), inference(resolution, [status(thm)], [c_8, c_115])).
% 2.82/1.44  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.82/1.44  tff(c_167, plain, (![A_72, B_73]: (m1_subset_1('#skF_2'(A_72), B_73) | ~r1_tarski(A_72, B_73) | k1_xboole_0=A_72)), inference(resolution, [status(thm)], [c_154, c_10])).
% 2.82/1.44  tff(c_48, plain, (![D_46]: (~r2_hidden(D_46, k1_relset_1('#skF_4', '#skF_3', '#skF_5')) | ~m1_subset_1(D_46, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.82/1.44  tff(c_53, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.82/1.44  tff(c_93, plain, (~m1_subset_1('#skF_2'(k1_relset_1('#skF_4', '#skF_3', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_53])).
% 2.82/1.44  tff(c_185, plain, (~r1_tarski(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), '#skF_4') | k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_167, c_93])).
% 2.82/1.44  tff(c_287, plain, (~r1_tarski(k1_relset_1('#skF_4', '#skF_3', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_185])).
% 2.82/1.44  tff(c_313, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_287])).
% 2.82/1.44  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_313])).
% 2.82/1.44  tff(c_321, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_185])).
% 2.82/1.44  tff(c_331, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.44  tff(c_350, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_331])).
% 2.82/1.44  tff(c_356, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_321, c_350])).
% 2.82/1.44  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_356])).
% 2.82/1.44  tff(c_359, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_53])).
% 2.82/1.44  tff(c_599, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.82/1.44  tff(c_618, plain, (k1_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_599])).
% 2.82/1.44  tff(c_624, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_359, c_618])).
% 2.82/1.44  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_624])).
% 2.82/1.44  tff(c_627, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_67])).
% 2.82/1.44  tff(c_735, plain, (![A_156, B_157, C_158]: (k2_relset_1(A_156, B_157, C_158)=k2_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.82/1.44  tff(c_746, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_735])).
% 2.82/1.44  tff(c_750, plain, (k2_relset_1('#skF_4', '#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_627, c_746])).
% 2.82/1.44  tff(c_752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_750])).
% 2.82/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.44  
% 2.82/1.44  Inference rules
% 2.82/1.44  ----------------------
% 2.82/1.44  #Ref     : 0
% 2.82/1.44  #Sup     : 143
% 2.82/1.44  #Fact    : 0
% 2.82/1.44  #Define  : 0
% 2.82/1.44  #Split   : 6
% 2.82/1.44  #Chain   : 0
% 2.82/1.44  #Close   : 0
% 2.82/1.44  
% 2.82/1.44  Ordering : KBO
% 2.82/1.44  
% 2.82/1.44  Simplification rules
% 2.82/1.44  ----------------------
% 2.82/1.44  #Subsume      : 7
% 2.82/1.44  #Demod        : 31
% 2.82/1.44  #Tautology    : 24
% 2.82/1.44  #SimpNegUnit  : 4
% 2.82/1.44  #BackRed      : 12
% 2.82/1.44  
% 2.82/1.44  #Partial instantiations: 0
% 2.82/1.44  #Strategies tried      : 1
% 2.82/1.44  
% 2.82/1.44  Timing (in seconds)
% 2.82/1.44  ----------------------
% 2.82/1.45  Preprocessing        : 0.31
% 2.82/1.45  Parsing              : 0.17
% 2.82/1.45  CNF conversion       : 0.02
% 2.82/1.45  Main loop            : 0.35
% 2.82/1.45  Inferencing          : 0.14
% 2.82/1.45  Reduction            : 0.10
% 2.82/1.45  Demodulation         : 0.06
% 2.82/1.45  BG Simplification    : 0.02
% 2.82/1.45  Subsumption          : 0.06
% 2.82/1.45  Abstraction          : 0.02
% 2.82/1.45  MUC search           : 0.00
% 2.82/1.45  Cooper               : 0.00
% 2.82/1.45  Total                : 0.70
% 2.82/1.45  Index Insertion      : 0.00
% 2.82/1.45  Index Deletion       : 0.00
% 2.82/1.45  Index Matching       : 0.00
% 2.82/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
