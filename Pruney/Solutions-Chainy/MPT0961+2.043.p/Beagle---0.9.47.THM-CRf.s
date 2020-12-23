%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:47 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 419 expanded)
%              Number of leaves         :   29 ( 152 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 (1046 expanded)
%              Number of equality atoms :   46 ( 327 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_85,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_987,plain,(
    ! [A_118] :
      ( r1_tarski(A_118,k2_zfmisc_1(k1_relat_1(A_118),k2_relat_1(A_118)))
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_234,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_340,plain,(
    ! [A_70,B_71,A_72] :
      ( k1_relset_1(A_70,B_71,A_72) = k1_relat_1(A_72)
      | ~ r1_tarski(A_72,k2_zfmisc_1(A_70,B_71)) ) ),
    inference(resolution,[status(thm)],[c_20,c_234])).

tff(c_363,plain,(
    ! [A_12] :
      ( k1_relset_1(k1_relat_1(A_12),k2_relat_1(A_12),A_12) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_24,c_340])).

tff(c_301,plain,(
    ! [B_63,C_64,A_65] :
      ( k1_xboole_0 = B_63
      | v1_funct_2(C_64,A_65,B_63)
      | k1_relset_1(A_65,B_63,C_64) != A_65
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_637,plain,(
    ! [B_98,A_99,A_100] :
      ( k1_xboole_0 = B_98
      | v1_funct_2(A_99,A_100,B_98)
      | k1_relset_1(A_100,B_98,A_99) != A_100
      | ~ r1_tarski(A_99,k2_zfmisc_1(A_100,B_98)) ) ),
    inference(resolution,[status(thm)],[c_20,c_301])).

tff(c_729,plain,(
    ! [A_104] :
      ( k2_relat_1(A_104) = k1_xboole_0
      | v1_funct_2(A_104,k1_relat_1(A_104),k2_relat_1(A_104))
      | k1_relset_1(k1_relat_1(A_104),k2_relat_1(A_104),A_104) != k1_relat_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_24,c_637])).

tff(c_50,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_84,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_736,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_729,c_84])).

tff(c_754,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_736])).

tff(c_763,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_754])).

tff(c_766,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_763])).

tff(c_770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_766])).

tff(c_771,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_754])).

tff(c_153,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40)))
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_162,plain,(
    ! [A_40] :
      ( k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40)) = A_40
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40)),A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(resolution,[status(thm)],[c_153,c_2])).

tff(c_780,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) = '#skF_1'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0),'#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_162])).

tff(c_792,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8,c_12,c_12,c_771,c_780])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_158,plain,(
    ! [A_13] :
      ( r1_tarski(k6_relat_1(A_13),k2_zfmisc_1(k1_relat_1(k6_relat_1(A_13)),A_13))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_153])).

tff(c_167,plain,(
    ! [A_41] : r1_tarski(k6_relat_1(A_41),k2_zfmisc_1(A_41,A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_158])).

tff(c_173,plain,(
    r1_tarski(k6_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_167])).

tff(c_130,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_184,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_173,c_139])).

tff(c_199,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_26])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_248,plain,(
    ! [A_45,B_46] : k1_relset_1(A_45,B_46,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_234])).

tff(c_251,plain,(
    ! [A_45,B_46] : k1_relset_1(A_45,B_46,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_248])).

tff(c_40,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_421,plain,(
    ! [C_75,B_76] :
      ( v1_funct_2(C_75,k1_xboole_0,B_76)
      | k1_relset_1(k1_xboole_0,B_76,C_75) != k1_xboole_0
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_427,plain,(
    ! [B_76] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_76)
      | k1_relset_1(k1_xboole_0,B_76,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_421])).

tff(c_431,plain,(
    ! [B_76] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_427])).

tff(c_810,plain,(
    ! [B_76] : v1_funct_2('#skF_1','#skF_1',B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_792,c_431])).

tff(c_821,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_792,c_199])).

tff(c_773,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_84])).

tff(c_857,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_773])).

tff(c_887,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_857])).

tff(c_925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_887])).

tff(c_926,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_965,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_20,c_926])).

tff(c_992,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_987,c_965])).

tff(c_1003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_992])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:25:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.41  
% 3.00/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.42  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.00/1.42  
% 3.00/1.42  %Foreground sorts:
% 3.00/1.42  
% 3.00/1.42  
% 3.00/1.42  %Background operators:
% 3.00/1.42  
% 3.00/1.42  
% 3.00/1.42  %Foreground operators:
% 3.00/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.00/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.00/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.00/1.42  tff('#skF_1', type, '#skF_1': $i).
% 3.00/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.00/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.00/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.42  
% 3.22/1.43  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.22/1.43  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.22/1.43  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.22/1.43  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.22/1.43  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.22/1.43  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.22/1.43  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.22/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.43  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.22/1.43  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.22/1.43  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.22/1.43  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.22/1.43  tff(c_987, plain, (![A_118]: (r1_tarski(A_118, k2_zfmisc_1(k1_relat_1(A_118), k2_relat_1(A_118))) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.43  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.22/1.43  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.22/1.43  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.43  tff(c_24, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.43  tff(c_234, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.22/1.43  tff(c_340, plain, (![A_70, B_71, A_72]: (k1_relset_1(A_70, B_71, A_72)=k1_relat_1(A_72) | ~r1_tarski(A_72, k2_zfmisc_1(A_70, B_71)))), inference(resolution, [status(thm)], [c_20, c_234])).
% 3.22/1.43  tff(c_363, plain, (![A_12]: (k1_relset_1(k1_relat_1(A_12), k2_relat_1(A_12), A_12)=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_24, c_340])).
% 3.22/1.43  tff(c_301, plain, (![B_63, C_64, A_65]: (k1_xboole_0=B_63 | v1_funct_2(C_64, A_65, B_63) | k1_relset_1(A_65, B_63, C_64)!=A_65 | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.22/1.43  tff(c_637, plain, (![B_98, A_99, A_100]: (k1_xboole_0=B_98 | v1_funct_2(A_99, A_100, B_98) | k1_relset_1(A_100, B_98, A_99)!=A_100 | ~r1_tarski(A_99, k2_zfmisc_1(A_100, B_98)))), inference(resolution, [status(thm)], [c_20, c_301])).
% 3.22/1.43  tff(c_729, plain, (![A_104]: (k2_relat_1(A_104)=k1_xboole_0 | v1_funct_2(A_104, k1_relat_1(A_104), k2_relat_1(A_104)) | k1_relset_1(k1_relat_1(A_104), k2_relat_1(A_104), A_104)!=k1_relat_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_24, c_637])).
% 3.22/1.43  tff(c_50, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.22/1.43  tff(c_48, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.22/1.43  tff(c_54, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 3.22/1.43  tff(c_84, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_54])).
% 3.22/1.43  tff(c_736, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_729, c_84])).
% 3.22/1.43  tff(c_754, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_736])).
% 3.22/1.43  tff(c_763, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_754])).
% 3.22/1.43  tff(c_766, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_363, c_763])).
% 3.22/1.43  tff(c_770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_766])).
% 3.22/1.43  tff(c_771, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_754])).
% 3.22/1.43  tff(c_153, plain, (![A_40]: (r1_tarski(A_40, k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40))) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.22/1.43  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.43  tff(c_162, plain, (![A_40]: (k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40))=A_40 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)), A_40) | ~v1_relat_1(A_40))), inference(resolution, [status(thm)], [c_153, c_2])).
% 3.22/1.43  tff(c_780, plain, (k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0), '#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_771, c_162])).
% 3.22/1.43  tff(c_792, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_8, c_12, c_12, c_771, c_780])).
% 3.22/1.43  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.22/1.43  tff(c_30, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.22/1.43  tff(c_26, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.43  tff(c_28, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.43  tff(c_158, plain, (![A_13]: (r1_tarski(k6_relat_1(A_13), k2_zfmisc_1(k1_relat_1(k6_relat_1(A_13)), A_13)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_153])).
% 3.22/1.43  tff(c_167, plain, (![A_41]: (r1_tarski(k6_relat_1(A_41), k2_zfmisc_1(A_41, A_41)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_158])).
% 3.22/1.43  tff(c_173, plain, (r1_tarski(k6_relat_1(k1_xboole_0), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_167])).
% 3.22/1.43  tff(c_130, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.43  tff(c_139, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_130])).
% 3.22/1.43  tff(c_184, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_173, c_139])).
% 3.22/1.43  tff(c_199, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_184, c_26])).
% 3.22/1.43  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.43  tff(c_248, plain, (![A_45, B_46]: (k1_relset_1(A_45, B_46, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_234])).
% 3.22/1.43  tff(c_251, plain, (![A_45, B_46]: (k1_relset_1(A_45, B_46, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_199, c_248])).
% 3.22/1.43  tff(c_40, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.22/1.43  tff(c_421, plain, (![C_75, B_76]: (v1_funct_2(C_75, k1_xboole_0, B_76) | k1_relset_1(k1_xboole_0, B_76, C_75)!=k1_xboole_0 | ~m1_subset_1(C_75, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 3.22/1.43  tff(c_427, plain, (![B_76]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_76) | k1_relset_1(k1_xboole_0, B_76, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_421])).
% 3.22/1.43  tff(c_431, plain, (![B_76]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_427])).
% 3.22/1.43  tff(c_810, plain, (![B_76]: (v1_funct_2('#skF_1', '#skF_1', B_76))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_792, c_431])).
% 3.22/1.43  tff(c_821, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_792, c_792, c_199])).
% 3.22/1.43  tff(c_773, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_771, c_84])).
% 3.22/1.43  tff(c_857, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_792, c_773])).
% 3.22/1.43  tff(c_887, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_821, c_857])).
% 3.22/1.43  tff(c_925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_810, c_887])).
% 3.22/1.43  tff(c_926, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_54])).
% 3.22/1.43  tff(c_965, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_926])).
% 3.22/1.43  tff(c_992, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_987, c_965])).
% 3.22/1.43  tff(c_1003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_992])).
% 3.22/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.43  
% 3.22/1.43  Inference rules
% 3.22/1.43  ----------------------
% 3.22/1.43  #Ref     : 0
% 3.22/1.43  #Sup     : 189
% 3.22/1.43  #Fact    : 0
% 3.22/1.43  #Define  : 0
% 3.22/1.43  #Split   : 2
% 3.22/1.43  #Chain   : 0
% 3.22/1.43  #Close   : 0
% 3.22/1.43  
% 3.22/1.43  Ordering : KBO
% 3.22/1.43  
% 3.22/1.43  Simplification rules
% 3.22/1.43  ----------------------
% 3.22/1.43  #Subsume      : 15
% 3.22/1.43  #Demod        : 320
% 3.22/1.43  #Tautology    : 125
% 3.22/1.43  #SimpNegUnit  : 0
% 3.22/1.43  #BackRed      : 38
% 3.22/1.43  
% 3.22/1.43  #Partial instantiations: 0
% 3.22/1.43  #Strategies tried      : 1
% 3.22/1.44  
% 3.22/1.44  Timing (in seconds)
% 3.22/1.44  ----------------------
% 3.22/1.44  Preprocessing        : 0.32
% 3.22/1.44  Parsing              : 0.17
% 3.22/1.44  CNF conversion       : 0.02
% 3.22/1.44  Main loop            : 0.36
% 3.22/1.44  Inferencing          : 0.12
% 3.22/1.44  Reduction            : 0.12
% 3.22/1.44  Demodulation         : 0.09
% 3.22/1.44  BG Simplification    : 0.02
% 3.22/1.44  Subsumption          : 0.06
% 3.22/1.44  Abstraction          : 0.02
% 3.22/1.44  MUC search           : 0.00
% 3.22/1.44  Cooper               : 0.00
% 3.22/1.44  Total                : 0.72
% 3.22/1.44  Index Insertion      : 0.00
% 3.22/1.44  Index Deletion       : 0.00
% 3.22/1.44  Index Matching       : 0.00
% 3.22/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
