%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 144 expanded)
%              Number of leaves         :   29 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  130 ( 332 expanded)
%              Number of equality atoms :   47 (  98 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_44,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5293,plain,(
    ! [C_10304,A_10305,B_10306] :
      ( m1_subset_1(C_10304,k1_zfmisc_1(k2_zfmisc_1(A_10305,B_10306)))
      | ~ r1_tarski(k2_relat_1(C_10304),B_10306)
      | ~ r1_tarski(k1_relat_1(C_10304),A_10305)
      | ~ v1_relat_1(C_10304) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_16,B_17] : v1_relat_1('#skF_1'(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [A_16,B_17] : v4_relat_1('#skF_1'(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4868,plain,(
    ! [B_10256,A_10257] :
      ( k7_relat_1(B_10256,A_10257) = B_10256
      | ~ v4_relat_1(B_10256,A_10257)
      | ~ v1_relat_1(B_10256) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4871,plain,(
    ! [A_16,B_17] :
      ( k7_relat_1('#skF_1'(A_16,B_17),A_16) = '#skF_1'(A_16,B_17)
      | ~ v1_relat_1('#skF_1'(A_16,B_17)) ) ),
    inference(resolution,[status(thm)],[c_42,c_4868])).

tff(c_4875,plain,(
    ! [A_10258,B_10259] : k7_relat_1('#skF_1'(A_10258,B_10259),A_10258) = '#skF_1'(A_10258,B_10259) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4871])).

tff(c_385,plain,(
    ! [C_64,A_65,B_66] :
      ( m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ r1_tarski(k2_relat_1(C_64),B_66)
      | ~ r1_tarski(k1_relat_1(C_64),A_65)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( k1_relset_1(A_7,B_8,C_9) = k1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_510,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ r1_tarski(k2_relat_1(C_80),B_79)
      | ~ r1_tarski(k1_relat_1(C_80),A_78)
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_385,c_20])).

tff(c_832,plain,(
    ! [A_470,C_471] :
      ( k1_relset_1(A_470,k2_relat_1(C_471),C_471) = k1_relat_1(C_471)
      | ~ r1_tarski(k1_relat_1(C_471),A_470)
      | ~ v1_relat_1(C_471) ) ),
    inference(resolution,[status(thm)],[c_6,c_510])).

tff(c_846,plain,(
    ! [C_471] :
      ( k1_relset_1(k1_relat_1(C_471),k2_relat_1(C_471),C_471) = k1_relat_1(C_471)
      | ~ v1_relat_1(C_471) ) ),
    inference(resolution,[status(thm)],[c_6,c_832])).

tff(c_91,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_91])).

tff(c_100,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_22,plain,(
    ! [C_12,A_10,B_11] :
      ( m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ r1_tarski(k2_relat_1(C_12),B_11)
      | ~ r1_tarski(k1_relat_1(C_12),A_10)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_490,plain,(
    ! [B_75,C_76,A_77] :
      ( k1_xboole_0 = B_75
      | v1_funct_2(C_76,A_77,B_75)
      | k1_relset_1(A_77,B_75,C_76) != A_77
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2566,plain,(
    ! [B_4578,C_4579,A_4580] :
      ( k1_xboole_0 = B_4578
      | v1_funct_2(C_4579,A_4580,B_4578)
      | k1_relset_1(A_4580,B_4578,C_4579) != A_4580
      | ~ r1_tarski(k2_relat_1(C_4579),B_4578)
      | ~ r1_tarski(k1_relat_1(C_4579),A_4580)
      | ~ v1_relat_1(C_4579) ) ),
    inference(resolution,[status(thm)],[c_22,c_490])).

tff(c_4752,plain,(
    ! [C_10245,A_10246] :
      ( k2_relat_1(C_10245) = k1_xboole_0
      | v1_funct_2(C_10245,A_10246,k2_relat_1(C_10245))
      | k1_relset_1(A_10246,k2_relat_1(C_10245),C_10245) != A_10246
      | ~ r1_tarski(k1_relat_1(C_10245),A_10246)
      | ~ v1_relat_1(C_10245) ) ),
    inference(resolution,[status(thm)],[c_6,c_2566])).

tff(c_50,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_69,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4765,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4752,c_69])).

tff(c_4778,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_4765])).

tff(c_4779,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_4778])).

tff(c_4784,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_4779])).

tff(c_4788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4784])).

tff(c_4789,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_71,plain,(
    ! [A_30] :
      ( k7_relat_1(A_30,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [A_16,B_17] : k7_relat_1('#skF_1'(A_16,B_17),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_4792,plain,(
    ! [A_16,B_17] : k7_relat_1('#skF_1'(A_16,B_17),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4789,c_4789,c_78])).

tff(c_4892,plain,(
    ! [B_10260] : '#skF_1'('#skF_2',B_10260) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4875,c_4792])).

tff(c_36,plain,(
    ! [A_16,B_17] : v1_funct_2('#skF_1'(A_16,B_17),A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4905,plain,(
    ! [B_10260] : v1_funct_2('#skF_2','#skF_2',B_10260) ),
    inference(superposition,[status(thm),theory(equality)],[c_4892,c_36])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4796,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4789,c_4789,c_14])).

tff(c_4790,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_4801,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4789,c_4790])).

tff(c_4802,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4801,c_69])).

tff(c_4816,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4796,c_4802])).

tff(c_4939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4905,c_4816])).

tff(c_4940,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5311,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_5293,c_4940])).

tff(c_5319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6,c_6,c_5311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.94  
% 4.92/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.94  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.92/1.94  
% 4.92/1.94  %Foreground sorts:
% 4.92/1.94  
% 4.92/1.94  
% 4.92/1.94  %Background operators:
% 4.92/1.94  
% 4.92/1.94  
% 4.92/1.94  %Foreground operators:
% 4.92/1.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.94  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.92/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.92/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.92/1.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.92/1.94  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.92/1.94  tff('#skF_2', type, '#skF_2': $i).
% 4.92/1.94  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.92/1.94  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.92/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.92/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.92/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.94  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.92/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.92/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.92/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.94  
% 4.92/1.95  tff(f_106, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 4.92/1.95  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.92/1.95  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.92/1.95  tff(f_95, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 4.92/1.95  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.92/1.95  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.92/1.95  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.92/1.95  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.92/1.95  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 4.92/1.95  tff(f_44, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.92/1.95  tff(c_52, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.92/1.95  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.92/1.95  tff(c_5293, plain, (![C_10304, A_10305, B_10306]: (m1_subset_1(C_10304, k1_zfmisc_1(k2_zfmisc_1(A_10305, B_10306))) | ~r1_tarski(k2_relat_1(C_10304), B_10306) | ~r1_tarski(k1_relat_1(C_10304), A_10305) | ~v1_relat_1(C_10304))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.92/1.95  tff(c_44, plain, (![A_16, B_17]: (v1_relat_1('#skF_1'(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.92/1.95  tff(c_42, plain, (![A_16, B_17]: (v4_relat_1('#skF_1'(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.92/1.95  tff(c_4868, plain, (![B_10256, A_10257]: (k7_relat_1(B_10256, A_10257)=B_10256 | ~v4_relat_1(B_10256, A_10257) | ~v1_relat_1(B_10256))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.92/1.95  tff(c_4871, plain, (![A_16, B_17]: (k7_relat_1('#skF_1'(A_16, B_17), A_16)='#skF_1'(A_16, B_17) | ~v1_relat_1('#skF_1'(A_16, B_17)))), inference(resolution, [status(thm)], [c_42, c_4868])).
% 4.92/1.95  tff(c_4875, plain, (![A_10258, B_10259]: (k7_relat_1('#skF_1'(A_10258, B_10259), A_10258)='#skF_1'(A_10258, B_10259))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4871])).
% 4.92/1.95  tff(c_385, plain, (![C_64, A_65, B_66]: (m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~r1_tarski(k2_relat_1(C_64), B_66) | ~r1_tarski(k1_relat_1(C_64), A_65) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.92/1.95  tff(c_20, plain, (![A_7, B_8, C_9]: (k1_relset_1(A_7, B_8, C_9)=k1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.92/1.95  tff(c_510, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~r1_tarski(k2_relat_1(C_80), B_79) | ~r1_tarski(k1_relat_1(C_80), A_78) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_385, c_20])).
% 4.92/1.95  tff(c_832, plain, (![A_470, C_471]: (k1_relset_1(A_470, k2_relat_1(C_471), C_471)=k1_relat_1(C_471) | ~r1_tarski(k1_relat_1(C_471), A_470) | ~v1_relat_1(C_471))), inference(resolution, [status(thm)], [c_6, c_510])).
% 4.92/1.95  tff(c_846, plain, (![C_471]: (k1_relset_1(k1_relat_1(C_471), k2_relat_1(C_471), C_471)=k1_relat_1(C_471) | ~v1_relat_1(C_471))), inference(resolution, [status(thm)], [c_6, c_832])).
% 4.92/1.95  tff(c_91, plain, (![A_33]: (k2_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.92/1.95  tff(c_99, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_52, c_91])).
% 4.92/1.95  tff(c_100, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_99])).
% 4.92/1.95  tff(c_22, plain, (![C_12, A_10, B_11]: (m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~r1_tarski(k2_relat_1(C_12), B_11) | ~r1_tarski(k1_relat_1(C_12), A_10) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.92/1.95  tff(c_490, plain, (![B_75, C_76, A_77]: (k1_xboole_0=B_75 | v1_funct_2(C_76, A_77, B_75) | k1_relset_1(A_77, B_75, C_76)!=A_77 | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_75))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.92/1.95  tff(c_2566, plain, (![B_4578, C_4579, A_4580]: (k1_xboole_0=B_4578 | v1_funct_2(C_4579, A_4580, B_4578) | k1_relset_1(A_4580, B_4578, C_4579)!=A_4580 | ~r1_tarski(k2_relat_1(C_4579), B_4578) | ~r1_tarski(k1_relat_1(C_4579), A_4580) | ~v1_relat_1(C_4579))), inference(resolution, [status(thm)], [c_22, c_490])).
% 4.92/1.95  tff(c_4752, plain, (![C_10245, A_10246]: (k2_relat_1(C_10245)=k1_xboole_0 | v1_funct_2(C_10245, A_10246, k2_relat_1(C_10245)) | k1_relset_1(A_10246, k2_relat_1(C_10245), C_10245)!=A_10246 | ~r1_tarski(k1_relat_1(C_10245), A_10246) | ~v1_relat_1(C_10245))), inference(resolution, [status(thm)], [c_6, c_2566])).
% 4.92/1.95  tff(c_50, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.92/1.95  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.92/1.95  tff(c_54, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 4.92/1.95  tff(c_69, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_54])).
% 4.92/1.95  tff(c_4765, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4752, c_69])).
% 4.92/1.95  tff(c_4778, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_4765])).
% 4.92/1.95  tff(c_4779, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_100, c_4778])).
% 4.92/1.95  tff(c_4784, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_846, c_4779])).
% 4.92/1.95  tff(c_4788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_4784])).
% 4.92/1.95  tff(c_4789, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_99])).
% 4.92/1.95  tff(c_71, plain, (![A_30]: (k7_relat_1(A_30, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.92/1.95  tff(c_78, plain, (![A_16, B_17]: (k7_relat_1('#skF_1'(A_16, B_17), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_71])).
% 4.92/1.95  tff(c_4792, plain, (![A_16, B_17]: (k7_relat_1('#skF_1'(A_16, B_17), '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4789, c_4789, c_78])).
% 4.92/1.95  tff(c_4892, plain, (![B_10260]: ('#skF_1'('#skF_2', B_10260)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4875, c_4792])).
% 4.92/1.95  tff(c_36, plain, (![A_16, B_17]: (v1_funct_2('#skF_1'(A_16, B_17), A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.92/1.95  tff(c_4905, plain, (![B_10260]: (v1_funct_2('#skF_2', '#skF_2', B_10260))), inference(superposition, [status(thm), theory('equality')], [c_4892, c_36])).
% 4.92/1.95  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.92/1.95  tff(c_4796, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4789, c_4789, c_14])).
% 4.92/1.95  tff(c_4790, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_99])).
% 4.92/1.95  tff(c_4801, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4789, c_4790])).
% 4.92/1.95  tff(c_4802, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4801, c_69])).
% 4.92/1.95  tff(c_4816, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4796, c_4802])).
% 4.92/1.95  tff(c_4939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4905, c_4816])).
% 4.92/1.95  tff(c_4940, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_54])).
% 4.92/1.95  tff(c_5311, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_5293, c_4940])).
% 4.92/1.95  tff(c_5319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_6, c_6, c_5311])).
% 4.92/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/1.95  
% 4.92/1.95  Inference rules
% 4.92/1.95  ----------------------
% 4.92/1.95  #Ref     : 0
% 4.92/1.95  #Sup     : 1104
% 4.92/1.95  #Fact    : 12
% 4.92/1.95  #Define  : 0
% 4.92/1.95  #Split   : 16
% 4.92/1.95  #Chain   : 0
% 4.92/1.95  #Close   : 0
% 4.92/1.95  
% 4.92/1.95  Ordering : KBO
% 4.92/1.95  
% 4.92/1.95  Simplification rules
% 4.92/1.95  ----------------------
% 4.92/1.95  #Subsume      : 586
% 4.92/1.95  #Demod        : 449
% 4.92/1.95  #Tautology    : 365
% 4.92/1.95  #SimpNegUnit  : 1
% 4.92/1.95  #BackRed      : 8
% 4.92/1.95  
% 4.92/1.95  #Partial instantiations: 836
% 4.92/1.95  #Strategies tried      : 1
% 4.92/1.95  
% 4.92/1.95  Timing (in seconds)
% 4.92/1.95  ----------------------
% 4.92/1.95  Preprocessing        : 0.31
% 4.92/1.95  Parsing              : 0.16
% 4.92/1.95  CNF conversion       : 0.02
% 4.92/1.95  Main loop            : 0.82
% 4.92/1.95  Inferencing          : 0.36
% 4.92/1.95  Reduction            : 0.23
% 4.92/1.96  Demodulation         : 0.16
% 4.92/1.96  BG Simplification    : 0.03
% 4.92/1.96  Subsumption          : 0.15
% 4.92/1.96  Abstraction          : 0.04
% 4.92/1.96  MUC search           : 0.00
% 4.92/1.96  Cooper               : 0.00
% 4.92/1.96  Total                : 1.16
% 4.92/1.96  Index Insertion      : 0.00
% 4.92/1.96  Index Deletion       : 0.00
% 4.92/1.96  Index Matching       : 0.00
% 4.92/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
