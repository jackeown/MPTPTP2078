%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:28 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 124 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 364 expanded)
%              Number of equality atoms :   14 (  37 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( B != k1_xboole_0
            & ? [D] :
                ( v1_funct_1(D)
                & v1_funct_2(D,B,A)
                & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A)) )
            & ~ v2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_92,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_86,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_74,plain,(
    ! [A_40] :
      ( v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_77,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_40])).

tff(c_80,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_77])).

tff(c_81,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_101,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_xboole_0(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_101])).

tff(c_115,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_110])).

tff(c_54,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_34,plain,(
    ! [A_24] : k6_relat_1(A_24) = k6_partfun1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_18,plain,(
    ! [A_8] : v2_funct_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_57,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_213,plain,(
    ! [F_74,B_73,E_76,A_72,D_75,C_71] :
      ( m1_subset_1(k1_partfun1(A_72,B_73,C_71,D_75,E_76,F_74),k1_zfmisc_1(k2_zfmisc_1(A_72,D_75)))
      | ~ m1_subset_1(F_74,k1_zfmisc_1(k2_zfmisc_1(C_71,D_75)))
      | ~ v1_funct_1(F_74)
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73)))
      | ~ v1_funct_1(E_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_23] : m1_subset_1(k6_partfun1(A_23),k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_138,plain,(
    ! [D_53,C_54,A_55,B_56] :
      ( D_53 = C_54
      | ~ r2_relset_1(A_55,B_56,C_54,D_53)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_144,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_42,c_138])).

tff(c_155,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_144])).

tff(c_163,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_224,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_213,c_163])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_48,c_44,c_224])).

tff(c_237,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_485,plain,(
    ! [A_143,C_144,D_142,E_146,B_145] :
      ( k1_xboole_0 = C_144
      | v2_funct_1(D_142)
      | ~ v2_funct_1(k1_partfun1(A_143,B_145,B_145,C_144,D_142,E_146))
      | ~ m1_subset_1(E_146,k1_zfmisc_1(k2_zfmisc_1(B_145,C_144)))
      | ~ v1_funct_2(E_146,B_145,C_144)
      | ~ v1_funct_1(E_146)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_145)))
      | ~ v1_funct_2(D_142,A_143,B_145)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_487,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_485])).

tff(c_492,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_48,c_46,c_44,c_57,c_487])).

tff(c_493,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_492])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : r1_xboole_0(A_2,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [B_41,A_42] :
      ( ~ r1_xboole_0(B_41,A_42)
      | ~ r1_tarski(B_41,A_42)
      | v1_xboole_0(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [A_43] :
      ( ~ r1_tarski(A_43,k1_xboole_0)
      | v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_499,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_92])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_499])).

tff(c_506,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_507,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_8,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_513,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_8])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_506,c_513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.50  
% 2.99/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.50  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.99/1.50  
% 2.99/1.50  %Foreground sorts:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Background operators:
% 2.99/1.50  
% 2.99/1.50  
% 2.99/1.50  %Foreground operators:
% 2.99/1.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.99/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.50  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.99/1.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.99/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.50  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.99/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.50  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.50  
% 3.13/1.52  tff(f_137, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~((~(B = k1_xboole_0) & (?[D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))))) & ~v2_funct_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_funct_2)).
% 3.13/1.52  tff(f_57, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.13/1.52  tff(f_66, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.13/1.52  tff(f_92, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.13/1.52  tff(f_59, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 3.13/1.52  tff(f_86, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.13/1.52  tff(f_90, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.13/1.52  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.13/1.52  tff(f_114, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 3.13/1.52  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.13/1.52  tff(f_29, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.13/1.52  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.13/1.52  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.13/1.52  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_74, plain, (![A_40]: (v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.13/1.52  tff(c_40, plain, (~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_77, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_74, c_40])).
% 3.13/1.52  tff(c_80, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_77])).
% 3.13/1.52  tff(c_81, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 3.13/1.52  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_101, plain, (![C_44, A_45, B_46]: (v1_xboole_0(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.13/1.52  tff(c_110, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_52, c_101])).
% 3.13/1.52  tff(c_115, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_81, c_110])).
% 3.13/1.52  tff(c_54, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_34, plain, (![A_24]: (k6_relat_1(A_24)=k6_partfun1(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.13/1.52  tff(c_18, plain, (![A_8]: (v2_funct_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.13/1.52  tff(c_57, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 3.13/1.52  tff(c_213, plain, (![F_74, B_73, E_76, A_72, D_75, C_71]: (m1_subset_1(k1_partfun1(A_72, B_73, C_71, D_75, E_76, F_74), k1_zfmisc_1(k2_zfmisc_1(A_72, D_75))) | ~m1_subset_1(F_74, k1_zfmisc_1(k2_zfmisc_1(C_71, D_75))) | ~v1_funct_1(F_74) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))) | ~v1_funct_1(E_76))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.13/1.52  tff(c_32, plain, (![A_23]: (m1_subset_1(k6_partfun1(A_23), k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.13/1.52  tff(c_42, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.13/1.52  tff(c_138, plain, (![D_53, C_54, A_55, B_56]: (D_53=C_54 | ~r2_relset_1(A_55, B_56, C_54, D_53) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.13/1.52  tff(c_144, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_42, c_138])).
% 3.13/1.52  tff(c_155, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_144])).
% 3.13/1.52  tff(c_163, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_155])).
% 3.13/1.52  tff(c_224, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_213, c_163])).
% 3.13/1.52  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_48, c_44, c_224])).
% 3.13/1.52  tff(c_237, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_155])).
% 3.13/1.52  tff(c_485, plain, (![A_143, C_144, D_142, E_146, B_145]: (k1_xboole_0=C_144 | v2_funct_1(D_142) | ~v2_funct_1(k1_partfun1(A_143, B_145, B_145, C_144, D_142, E_146)) | ~m1_subset_1(E_146, k1_zfmisc_1(k2_zfmisc_1(B_145, C_144))) | ~v1_funct_2(E_146, B_145, C_144) | ~v1_funct_1(E_146) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_145))) | ~v1_funct_2(D_142, A_143, B_145) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.13/1.52  tff(c_487, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_237, c_485])).
% 3.13/1.52  tff(c_492, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_48, c_46, c_44, c_57, c_487])).
% 3.13/1.52  tff(c_493, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_40, c_492])).
% 3.13/1.52  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.13/1.52  tff(c_4, plain, (![A_2]: (r1_xboole_0(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.13/1.52  tff(c_82, plain, (![B_41, A_42]: (~r1_xboole_0(B_41, A_42) | ~r1_tarski(B_41, A_42) | v1_xboole_0(B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.13/1.52  tff(c_87, plain, (![A_43]: (~r1_tarski(A_43, k1_xboole_0) | v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_4, c_82])).
% 3.13/1.52  tff(c_92, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_87])).
% 3.13/1.52  tff(c_499, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_92])).
% 3.13/1.52  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_115, c_499])).
% 3.13/1.52  tff(c_506, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 3.13/1.52  tff(c_507, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 3.13/1.52  tff(c_8, plain, (![A_5]: (v1_relat_1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.13/1.52  tff(c_513, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_507, c_8])).
% 3.13/1.52  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_506, c_513])).
% 3.13/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.52  
% 3.13/1.52  Inference rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Ref     : 0
% 3.13/1.52  #Sup     : 90
% 3.13/1.52  #Fact    : 0
% 3.13/1.52  #Define  : 0
% 3.13/1.52  #Split   : 3
% 3.13/1.52  #Chain   : 0
% 3.13/1.52  #Close   : 0
% 3.13/1.52  
% 3.13/1.52  Ordering : KBO
% 3.13/1.52  
% 3.13/1.52  Simplification rules
% 3.13/1.52  ----------------------
% 3.13/1.52  #Subsume      : 9
% 3.13/1.52  #Demod        : 73
% 3.13/1.52  #Tautology    : 13
% 3.13/1.52  #SimpNegUnit  : 4
% 3.13/1.52  #BackRed      : 10
% 3.13/1.52  
% 3.13/1.52  #Partial instantiations: 0
% 3.13/1.52  #Strategies tried      : 1
% 3.13/1.52  
% 3.13/1.52  Timing (in seconds)
% 3.13/1.52  ----------------------
% 3.13/1.52  Preprocessing        : 0.35
% 3.13/1.52  Parsing              : 0.19
% 3.13/1.52  CNF conversion       : 0.02
% 3.13/1.52  Main loop            : 0.32
% 3.13/1.52  Inferencing          : 0.12
% 3.13/1.52  Reduction            : 0.10
% 3.13/1.52  Demodulation         : 0.07
% 3.13/1.52  BG Simplification    : 0.02
% 3.13/1.52  Subsumption          : 0.06
% 3.13/1.52  Abstraction          : 0.01
% 3.13/1.52  MUC search           : 0.00
% 3.13/1.52  Cooper               : 0.00
% 3.13/1.52  Total                : 0.71
% 3.13/1.52  Index Insertion      : 0.00
% 3.13/1.52  Index Deletion       : 0.00
% 3.13/1.52  Index Matching       : 0.00
% 3.13/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
