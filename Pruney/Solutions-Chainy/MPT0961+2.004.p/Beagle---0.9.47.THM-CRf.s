%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:41 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 152 expanded)
%              Number of leaves         :   30 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 342 expanded)
%              Number of equality atoms :   38 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_115,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1628,plain,(
    ! [C_588,A_589,B_590] :
      ( m1_subset_1(C_588,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590)))
      | ~ r1_tarski(k2_relat_1(C_588),B_590)
      | ~ r1_tarski(k1_relat_1(C_588),A_589)
      | ~ v1_relat_1(C_588) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_408,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ r1_tarski(k2_relat_1(C_85),B_87)
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_486,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ r1_tarski(k2_relat_1(C_101),B_100)
      | ~ r1_tarski(k1_relat_1(C_101),A_99)
      | ~ v1_relat_1(C_101) ) ),
    inference(resolution,[status(thm)],[c_408,c_38])).

tff(c_552,plain,(
    ! [A_109,C_110] :
      ( k1_relset_1(A_109,k2_relat_1(C_110),C_110) = k1_relat_1(C_110)
      | ~ r1_tarski(k1_relat_1(C_110),A_109)
      | ~ v1_relat_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_8,c_486])).

tff(c_560,plain,(
    ! [C_110] :
      ( k1_relset_1(k1_relat_1(C_110),k2_relat_1(C_110),C_110) = k1_relat_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_8,c_552])).

tff(c_94,plain,(
    ! [A_38] :
      ( k2_relat_1(A_38) != k1_xboole_0
      | k1_xboole_0 = A_38
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_106,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_64,c_94])).

tff(c_107,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_40,plain,(
    ! [C_16,A_14,B_15] :
      ( m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ r1_tarski(k2_relat_1(C_16),B_15)
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_473,plain,(
    ! [B_94,C_95,A_96] :
      ( k1_xboole_0 = B_94
      | v1_funct_2(C_95,A_96,B_94)
      | k1_relset_1(A_96,B_94,C_95) != A_96
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_888,plain,(
    ! [B_475,C_476,A_477] :
      ( k1_xboole_0 = B_475
      | v1_funct_2(C_476,A_477,B_475)
      | k1_relset_1(A_477,B_475,C_476) != A_477
      | ~ r1_tarski(k2_relat_1(C_476),B_475)
      | ~ r1_tarski(k1_relat_1(C_476),A_477)
      | ~ v1_relat_1(C_476) ) ),
    inference(resolution,[status(thm)],[c_40,c_473])).

tff(c_934,plain,(
    ! [C_481,A_482] :
      ( k2_relat_1(C_481) = k1_xboole_0
      | v1_funct_2(C_481,A_482,k2_relat_1(C_481))
      | k1_relset_1(A_482,k2_relat_1(C_481),C_481) != A_482
      | ~ r1_tarski(k1_relat_1(C_481),A_482)
      | ~ v1_relat_1(C_481) ) ),
    inference(resolution,[status(thm)],[c_8,c_888])).

tff(c_62,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_66,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60])).

tff(c_82,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_945,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_934,c_82])).

tff(c_955,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8,c_945])).

tff(c_956,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_955])).

tff(c_961,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_956])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_961])).

tff(c_966,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_979,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_2])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_976,plain,(
    ! [A_3] : m1_subset_1('#skF_2',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_10])).

tff(c_1138,plain,(
    ! [C_508,A_509,B_510] :
      ( v1_partfun1(C_508,A_509)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(A_509,B_510)))
      | ~ v1_xboole_0(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1143,plain,(
    ! [A_509] :
      ( v1_partfun1('#skF_2',A_509)
      | ~ v1_xboole_0(A_509) ) ),
    inference(resolution,[status(thm)],[c_976,c_1138])).

tff(c_1295,plain,(
    ! [C_529,A_530,B_531] :
      ( v1_funct_2(C_529,A_530,B_531)
      | ~ v1_partfun1(C_529,A_530)
      | ~ v1_funct_1(C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_530,B_531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1299,plain,(
    ! [A_530,B_531] :
      ( v1_funct_2('#skF_2',A_530,B_531)
      | ~ v1_partfun1('#skF_2',A_530)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_976,c_1295])).

tff(c_1303,plain,(
    ! [A_532,B_533] :
      ( v1_funct_2('#skF_2',A_532,B_533)
      | ~ v1_partfun1('#skF_2',A_532) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1299])).

tff(c_16,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_977,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_966,c_16])).

tff(c_967,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_984,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_967])).

tff(c_985,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_82])).

tff(c_1009,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_977,c_985])).

tff(c_1307,plain,(
    ~ v1_partfun1('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_1303,c_1009])).

tff(c_1310,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1143,c_1307])).

tff(c_1314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1310])).

tff(c_1315,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1654,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1628,c_1315])).

tff(c_1665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8,c_8,c_1654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  
% 3.34/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.52  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.34/1.52  
% 3.34/1.52  %Foreground sorts:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Background operators:
% 3.34/1.52  
% 3.34/1.52  
% 3.34/1.52  %Foreground operators:
% 3.34/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.34/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.34/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.34/1.52  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.34/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.34/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.34/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.52  
% 3.34/1.53  tff(f_126, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.34/1.53  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.34/1.53  tff(f_80, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.34/1.53  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.34/1.53  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.34/1.53  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.34/1.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.34/1.53  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.34/1.53  tff(f_97, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.34/1.53  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.34/1.53  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.34/1.53  tff(c_64, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.34/1.53  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.34/1.53  tff(c_1628, plain, (![C_588, A_589, B_590]: (m1_subset_1(C_588, k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))) | ~r1_tarski(k2_relat_1(C_588), B_590) | ~r1_tarski(k1_relat_1(C_588), A_589) | ~v1_relat_1(C_588))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.53  tff(c_408, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~r1_tarski(k2_relat_1(C_85), B_87) | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.53  tff(c_38, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.34/1.53  tff(c_486, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~r1_tarski(k2_relat_1(C_101), B_100) | ~r1_tarski(k1_relat_1(C_101), A_99) | ~v1_relat_1(C_101))), inference(resolution, [status(thm)], [c_408, c_38])).
% 3.34/1.53  tff(c_552, plain, (![A_109, C_110]: (k1_relset_1(A_109, k2_relat_1(C_110), C_110)=k1_relat_1(C_110) | ~r1_tarski(k1_relat_1(C_110), A_109) | ~v1_relat_1(C_110))), inference(resolution, [status(thm)], [c_8, c_486])).
% 3.34/1.53  tff(c_560, plain, (![C_110]: (k1_relset_1(k1_relat_1(C_110), k2_relat_1(C_110), C_110)=k1_relat_1(C_110) | ~v1_relat_1(C_110))), inference(resolution, [status(thm)], [c_8, c_552])).
% 3.34/1.53  tff(c_94, plain, (![A_38]: (k2_relat_1(A_38)!=k1_xboole_0 | k1_xboole_0=A_38 | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.34/1.53  tff(c_106, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_64, c_94])).
% 3.34/1.53  tff(c_107, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_106])).
% 3.34/1.53  tff(c_40, plain, (![C_16, A_14, B_15]: (m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~r1_tarski(k2_relat_1(C_16), B_15) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.53  tff(c_473, plain, (![B_94, C_95, A_96]: (k1_xboole_0=B_94 | v1_funct_2(C_95, A_96, B_94) | k1_relset_1(A_96, B_94, C_95)!=A_96 | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_94))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.34/1.53  tff(c_888, plain, (![B_475, C_476, A_477]: (k1_xboole_0=B_475 | v1_funct_2(C_476, A_477, B_475) | k1_relset_1(A_477, B_475, C_476)!=A_477 | ~r1_tarski(k2_relat_1(C_476), B_475) | ~r1_tarski(k1_relat_1(C_476), A_477) | ~v1_relat_1(C_476))), inference(resolution, [status(thm)], [c_40, c_473])).
% 3.34/1.53  tff(c_934, plain, (![C_481, A_482]: (k2_relat_1(C_481)=k1_xboole_0 | v1_funct_2(C_481, A_482, k2_relat_1(C_481)) | k1_relset_1(A_482, k2_relat_1(C_481), C_481)!=A_482 | ~r1_tarski(k1_relat_1(C_481), A_482) | ~v1_relat_1(C_481))), inference(resolution, [status(thm)], [c_8, c_888])).
% 3.34/1.53  tff(c_62, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.34/1.53  tff(c_60, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.34/1.53  tff(c_66, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60])).
% 3.34/1.53  tff(c_82, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_66])).
% 3.34/1.53  tff(c_945, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_934, c_82])).
% 3.34/1.53  tff(c_955, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8, c_945])).
% 3.34/1.53  tff(c_956, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_107, c_955])).
% 3.34/1.53  tff(c_961, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_560, c_956])).
% 3.34/1.53  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_961])).
% 3.34/1.53  tff(c_966, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_106])).
% 3.34/1.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.34/1.53  tff(c_979, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_966, c_2])).
% 3.34/1.53  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.34/1.53  tff(c_976, plain, (![A_3]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_966, c_10])).
% 3.34/1.53  tff(c_1138, plain, (![C_508, A_509, B_510]: (v1_partfun1(C_508, A_509) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(A_509, B_510))) | ~v1_xboole_0(A_509))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.34/1.53  tff(c_1143, plain, (![A_509]: (v1_partfun1('#skF_2', A_509) | ~v1_xboole_0(A_509))), inference(resolution, [status(thm)], [c_976, c_1138])).
% 3.34/1.53  tff(c_1295, plain, (![C_529, A_530, B_531]: (v1_funct_2(C_529, A_530, B_531) | ~v1_partfun1(C_529, A_530) | ~v1_funct_1(C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_530, B_531))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.34/1.53  tff(c_1299, plain, (![A_530, B_531]: (v1_funct_2('#skF_2', A_530, B_531) | ~v1_partfun1('#skF_2', A_530) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_976, c_1295])).
% 3.34/1.53  tff(c_1303, plain, (![A_532, B_533]: (v1_funct_2('#skF_2', A_532, B_533) | ~v1_partfun1('#skF_2', A_532))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1299])).
% 3.34/1.53  tff(c_16, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.53  tff(c_977, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_966, c_966, c_16])).
% 3.34/1.53  tff(c_967, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_106])).
% 3.34/1.53  tff(c_984, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_966, c_967])).
% 3.34/1.53  tff(c_985, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_82])).
% 3.34/1.53  tff(c_1009, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_977, c_985])).
% 3.34/1.53  tff(c_1307, plain, (~v1_partfun1('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_1303, c_1009])).
% 3.34/1.53  tff(c_1310, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1143, c_1307])).
% 3.34/1.53  tff(c_1314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_979, c_1310])).
% 3.34/1.53  tff(c_1315, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_66])).
% 3.34/1.53  tff(c_1654, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1628, c_1315])).
% 3.34/1.53  tff(c_1665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_8, c_8, c_1654])).
% 3.34/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.53  
% 3.34/1.53  Inference rules
% 3.34/1.53  ----------------------
% 3.34/1.53  #Ref     : 0
% 3.34/1.53  #Sup     : 326
% 3.34/1.53  #Fact    : 0
% 3.34/1.53  #Define  : 0
% 3.34/1.53  #Split   : 7
% 3.34/1.53  #Chain   : 0
% 3.34/1.53  #Close   : 0
% 3.34/1.53  
% 3.34/1.53  Ordering : KBO
% 3.34/1.53  
% 3.34/1.53  Simplification rules
% 3.34/1.53  ----------------------
% 3.34/1.53  #Subsume      : 63
% 3.34/1.53  #Demod        : 337
% 3.34/1.53  #Tautology    : 180
% 3.34/1.53  #SimpNegUnit  : 1
% 3.34/1.53  #BackRed      : 24
% 3.34/1.53  
% 3.34/1.53  #Partial instantiations: 30
% 3.34/1.53  #Strategies tried      : 1
% 3.34/1.53  
% 3.34/1.53  Timing (in seconds)
% 3.34/1.53  ----------------------
% 3.34/1.54  Preprocessing        : 0.31
% 3.34/1.54  Parsing              : 0.16
% 3.34/1.54  CNF conversion       : 0.02
% 3.34/1.54  Main loop            : 0.47
% 3.34/1.54  Inferencing          : 0.18
% 3.34/1.54  Reduction            : 0.14
% 3.34/1.54  Demodulation         : 0.10
% 3.34/1.54  BG Simplification    : 0.02
% 3.34/1.54  Subsumption          : 0.09
% 3.34/1.54  Abstraction          : 0.02
% 3.34/1.54  MUC search           : 0.00
% 3.34/1.54  Cooper               : 0.00
% 3.34/1.54  Total                : 0.81
% 3.34/1.54  Index Insertion      : 0.00
% 3.34/1.54  Index Deletion       : 0.00
% 3.34/1.54  Index Matching       : 0.00
% 3.34/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
