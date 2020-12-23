%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:15 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 474 expanded)
%              Number of leaves         :   47 ( 186 expanded)
%              Depth                    :   15
%              Number of atoms          :  253 (1689 expanded)
%              Number of equality atoms :   61 ( 477 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_148,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_150,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_126,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_54,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_99,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_105,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_66,c_99])).

tff(c_114,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_151,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_162,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_151])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_108,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_72,c_99])).

tff(c_117,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_108])).

tff(c_163,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_151])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_22,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_233,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_242,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_233])).

tff(c_246,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_242])).

tff(c_212,plain,(
    ! [A_85] :
      ( k1_relat_1(k2_funct_1(A_85)) = k2_relat_1(A_85)
      | ~ v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_940,plain,(
    ! [A_162] :
      ( k9_relat_1(k2_funct_1(A_162),k2_relat_1(A_162)) = k2_relat_1(k2_funct_1(A_162))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_10])).

tff(c_956,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_940])).

tff(c_963,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76,c_60,c_956])).

tff(c_978,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_981,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_978])).

tff(c_985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76,c_981])).

tff(c_987,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_764,plain,(
    ! [E_143,A_141,B_142,F_140,C_138,D_139] :
      ( k1_partfun1(A_141,B_142,C_138,D_139,E_143,F_140) = k5_relat_1(E_143,F_140)
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_138,D_139)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_768,plain,(
    ! [A_141,B_142,E_143] :
      ( k1_partfun1(A_141,B_142,'#skF_2','#skF_1',E_143,'#skF_4') = k5_relat_1(E_143,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(E_143) ) ),
    inference(resolution,[status(thm)],[c_66,c_764])).

tff(c_821,plain,(
    ! [A_149,B_150,E_151] :
      ( k1_partfun1(A_149,B_150,'#skF_2','#skF_1',E_151,'#skF_4') = k5_relat_1(E_151,'#skF_4')
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_768])).

tff(c_830,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_821])).

tff(c_837,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_830])).

tff(c_52,plain,(
    ! [A_49] : k6_relat_1(A_49) = k6_partfun1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_44,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_77,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44])).

tff(c_62,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_513,plain,(
    ! [D_105,C_106,A_107,B_108] :
      ( D_105 = C_106
      | ~ r2_relset_1(A_107,B_108,C_106,D_105)
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_521,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_62,c_513])).

tff(c_536,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_521])).

tff(c_539,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_844,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_539])).

tff(c_855,plain,(
    ! [A_152,D_155,F_154,E_156,B_153,C_157] :
      ( m1_subset_1(k1_partfun1(A_152,B_153,C_157,D_155,E_156,F_154),k1_zfmisc_1(k2_zfmisc_1(A_152,D_155)))
      | ~ m1_subset_1(F_154,k1_zfmisc_1(k2_zfmisc_1(C_157,D_155)))
      | ~ v1_funct_1(F_154)
      | ~ m1_subset_1(E_156,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_1(E_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_885,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_837,c_855])).

tff(c_902,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_885])).

tff(c_905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_902])).

tff(c_906,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_1066,plain,(
    ! [D_173,E_177,F_174,A_175,C_172,B_176] :
      ( k1_partfun1(A_175,B_176,C_172,D_173,E_177,F_174) = k5_relat_1(E_177,F_174)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(C_172,D_173)))
      | ~ v1_funct_1(F_174)
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_funct_1(E_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1070,plain,(
    ! [A_175,B_176,E_177] :
      ( k1_partfun1(A_175,B_176,'#skF_2','#skF_1',E_177,'#skF_4') = k5_relat_1(E_177,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_funct_1(E_177) ) ),
    inference(resolution,[status(thm)],[c_66,c_1066])).

tff(c_1303,plain,(
    ! [A_200,B_201,E_202] :
      ( k1_partfun1(A_200,B_201,'#skF_2','#skF_1',E_202,'#skF_4') = k5_relat_1(E_202,'#skF_4')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201)))
      | ~ v1_funct_1(E_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1070])).

tff(c_1318,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_1303])).

tff(c_1329,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_906,c_1318])).

tff(c_30,plain,(
    ! [A_25] :
      ( k5_relat_1(k2_funct_1(A_25),A_25) = k6_relat_1(k2_relat_1(A_25))
      | ~ v2_funct_1(A_25)
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_329,plain,(
    ! [A_96] :
      ( k5_relat_1(k2_funct_1(A_96),A_96) = k6_partfun1(k2_relat_1(A_96))
      | ~ v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30])).

tff(c_14,plain,(
    ! [A_10,B_14,C_16] :
      ( k5_relat_1(k5_relat_1(A_10,B_14),C_16) = k5_relat_1(A_10,k5_relat_1(B_14,C_16))
      | ~ v1_relat_1(C_16)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2653,plain,(
    ! [A_239,C_240] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_239)),C_240) = k5_relat_1(k2_funct_1(A_239),k5_relat_1(A_239,C_240))
      | ~ v1_relat_1(C_240)
      | ~ v1_relat_1(A_239)
      | ~ v1_relat_1(k2_funct_1(A_239))
      | ~ v2_funct_1(A_239)
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_14])).

tff(c_2805,plain,(
    ! [C_240] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_240)) = k5_relat_1(k6_partfun1('#skF_2'),C_240)
      | ~ v1_relat_1(C_240)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_2653])).

tff(c_3307,plain,(
    ! [C_255] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_255)) = k5_relat_1(k6_partfun1('#skF_2'),C_255)
      | ~ v1_relat_1(C_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76,c_60,c_987,c_117,c_2805])).

tff(c_3334,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_3307])).

tff(c_3359,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_3334])).

tff(c_26,plain,(
    ! [A_24] :
      ( k2_relat_1(k2_funct_1(A_24)) = k1_relat_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k5_relat_1(B_20,k6_relat_1(A_19)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_208,plain,(
    ! [B_83,A_84] :
      ( k5_relat_1(B_83,k6_partfun1(A_84)) = B_83
      | ~ r1_tarski(k2_relat_1(B_83),A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_211,plain,(
    ! [A_24,A_84] :
      ( k5_relat_1(k2_funct_1(A_24),k6_partfun1(A_84)) = k2_funct_1(A_24)
      | ~ r1_tarski(k1_relat_1(A_24),A_84)
      | ~ v1_relat_1(k2_funct_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_208])).

tff(c_3404,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3359,c_211])).

tff(c_3425,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_76,c_60,c_987,c_3404])).

tff(c_3433,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3425])).

tff(c_3436,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_3433])).

tff(c_3440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_163,c_3436])).

tff(c_3441,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3425])).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = B_18
      | ~ r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_181,plain,(
    ! [A_77,B_78] :
      ( k5_relat_1(k6_partfun1(A_77),B_78) = B_78
      | ~ r1_tarski(k1_relat_1(B_78),A_77)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_16])).

tff(c_185,plain,(
    ! [A_4,B_5] :
      ( k5_relat_1(k6_partfun1(A_4),B_5) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_3506,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3441,c_185])).

tff(c_3523,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_162,c_3506])).

tff(c_3525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3523])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:54:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.16  
% 5.75/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.16  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.75/2.16  
% 5.75/2.16  %Foreground sorts:
% 5.75/2.16  
% 5.75/2.16  
% 5.75/2.16  %Background operators:
% 5.75/2.16  
% 5.75/2.16  
% 5.75/2.16  %Foreground operators:
% 5.75/2.16  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.75/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.75/2.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.75/2.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.75/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.16  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.75/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.16  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.75/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.75/2.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.75/2.16  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.75/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.75/2.16  tff('#skF_2', type, '#skF_2': $i).
% 5.75/2.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.75/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.16  tff('#skF_1', type, '#skF_1': $i).
% 5.75/2.16  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.75/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.16  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 5.75/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.16  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.75/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.75/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.75/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.75/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.16  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.75/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.75/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.16  
% 5.75/2.18  tff(f_176, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 5.75/2.18  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.75/2.18  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.75/2.18  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.75/2.18  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.75/2.18  tff(f_78, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 5.75/2.18  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.75/2.18  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 5.75/2.18  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 5.75/2.18  tff(f_148, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 5.75/2.18  tff(f_150, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 5.75/2.18  tff(f_126, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 5.75/2.18  tff(f_124, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.75/2.18  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 5.75/2.18  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 5.75/2.18  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 5.75/2.18  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 5.75/2.18  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 5.75/2.18  tff(c_54, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.75/2.18  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_99, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.75/2.18  tff(c_105, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_66, c_99])).
% 5.75/2.18  tff(c_114, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_105])).
% 5.75/2.18  tff(c_151, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.75/2.18  tff(c_162, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_151])).
% 5.75/2.18  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_108, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_72, c_99])).
% 5.75/2.18  tff(c_117, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_108])).
% 5.75/2.18  tff(c_163, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_151])).
% 5.75/2.18  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.75/2.18  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_22, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.75/2.18  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_233, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.75/2.18  tff(c_242, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_233])).
% 5.75/2.18  tff(c_246, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_242])).
% 5.75/2.18  tff(c_212, plain, (![A_85]: (k1_relat_1(k2_funct_1(A_85))=k2_relat_1(A_85) | ~v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.75/2.18  tff(c_10, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.75/2.18  tff(c_940, plain, (![A_162]: (k9_relat_1(k2_funct_1(A_162), k2_relat_1(A_162))=k2_relat_1(k2_funct_1(A_162)) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_212, c_10])).
% 5.75/2.18  tff(c_956, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_246, c_940])).
% 5.75/2.18  tff(c_963, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76, c_60, c_956])).
% 5.75/2.18  tff(c_978, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_963])).
% 5.75/2.18  tff(c_981, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_978])).
% 5.75/2.18  tff(c_985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_76, c_981])).
% 5.75/2.18  tff(c_987, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_963])).
% 5.75/2.18  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_764, plain, (![E_143, A_141, B_142, F_140, C_138, D_139]: (k1_partfun1(A_141, B_142, C_138, D_139, E_143, F_140)=k5_relat_1(E_143, F_140) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_138, D_139))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(E_143))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.75/2.18  tff(c_768, plain, (![A_141, B_142, E_143]: (k1_partfun1(A_141, B_142, '#skF_2', '#skF_1', E_143, '#skF_4')=k5_relat_1(E_143, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(E_143))), inference(resolution, [status(thm)], [c_66, c_764])).
% 5.75/2.18  tff(c_821, plain, (![A_149, B_150, E_151]: (k1_partfun1(A_149, B_150, '#skF_2', '#skF_1', E_151, '#skF_4')=k5_relat_1(E_151, '#skF_4') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(E_151))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_768])).
% 5.75/2.18  tff(c_830, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_821])).
% 5.75/2.18  tff(c_837, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_830])).
% 5.75/2.18  tff(c_52, plain, (![A_49]: (k6_relat_1(A_49)=k6_partfun1(A_49))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.75/2.18  tff(c_44, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.75/2.18  tff(c_77, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44])).
% 5.75/2.18  tff(c_62, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.75/2.18  tff(c_513, plain, (![D_105, C_106, A_107, B_108]: (D_105=C_106 | ~r2_relset_1(A_107, B_108, C_106, D_105) | ~m1_subset_1(D_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 5.75/2.18  tff(c_521, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_62, c_513])).
% 5.75/2.18  tff(c_536, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_521])).
% 5.75/2.18  tff(c_539, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_536])).
% 5.75/2.18  tff(c_844, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_837, c_539])).
% 5.75/2.18  tff(c_855, plain, (![A_152, D_155, F_154, E_156, B_153, C_157]: (m1_subset_1(k1_partfun1(A_152, B_153, C_157, D_155, E_156, F_154), k1_zfmisc_1(k2_zfmisc_1(A_152, D_155))) | ~m1_subset_1(F_154, k1_zfmisc_1(k2_zfmisc_1(C_157, D_155))) | ~v1_funct_1(F_154) | ~m1_subset_1(E_156, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_1(E_156))), inference(cnfTransformation, [status(thm)], [f_138])).
% 5.75/2.18  tff(c_885, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_837, c_855])).
% 5.75/2.18  tff(c_902, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_885])).
% 5.75/2.18  tff(c_905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_902])).
% 5.75/2.18  tff(c_906, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_536])).
% 5.75/2.18  tff(c_1066, plain, (![D_173, E_177, F_174, A_175, C_172, B_176]: (k1_partfun1(A_175, B_176, C_172, D_173, E_177, F_174)=k5_relat_1(E_177, F_174) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(C_172, D_173))) | ~v1_funct_1(F_174) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_funct_1(E_177))), inference(cnfTransformation, [status(thm)], [f_148])).
% 5.75/2.18  tff(c_1070, plain, (![A_175, B_176, E_177]: (k1_partfun1(A_175, B_176, '#skF_2', '#skF_1', E_177, '#skF_4')=k5_relat_1(E_177, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_funct_1(E_177))), inference(resolution, [status(thm)], [c_66, c_1066])).
% 5.75/2.18  tff(c_1303, plain, (![A_200, B_201, E_202]: (k1_partfun1(A_200, B_201, '#skF_2', '#skF_1', E_202, '#skF_4')=k5_relat_1(E_202, '#skF_4') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))) | ~v1_funct_1(E_202))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1070])).
% 5.75/2.18  tff(c_1318, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_72, c_1303])).
% 5.75/2.18  tff(c_1329, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_906, c_1318])).
% 5.75/2.18  tff(c_30, plain, (![A_25]: (k5_relat_1(k2_funct_1(A_25), A_25)=k6_relat_1(k2_relat_1(A_25)) | ~v2_funct_1(A_25) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.75/2.18  tff(c_329, plain, (![A_96]: (k5_relat_1(k2_funct_1(A_96), A_96)=k6_partfun1(k2_relat_1(A_96)) | ~v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30])).
% 5.75/2.18  tff(c_14, plain, (![A_10, B_14, C_16]: (k5_relat_1(k5_relat_1(A_10, B_14), C_16)=k5_relat_1(A_10, k5_relat_1(B_14, C_16)) | ~v1_relat_1(C_16) | ~v1_relat_1(B_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.75/2.18  tff(c_2653, plain, (![A_239, C_240]: (k5_relat_1(k6_partfun1(k2_relat_1(A_239)), C_240)=k5_relat_1(k2_funct_1(A_239), k5_relat_1(A_239, C_240)) | ~v1_relat_1(C_240) | ~v1_relat_1(A_239) | ~v1_relat_1(k2_funct_1(A_239)) | ~v2_funct_1(A_239) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(superposition, [status(thm), theory('equality')], [c_329, c_14])).
% 5.75/2.18  tff(c_2805, plain, (![C_240]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_240))=k5_relat_1(k6_partfun1('#skF_2'), C_240) | ~v1_relat_1(C_240) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_2653])).
% 5.75/2.18  tff(c_3307, plain, (![C_255]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_255))=k5_relat_1(k6_partfun1('#skF_2'), C_255) | ~v1_relat_1(C_255))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76, c_60, c_987, c_117, c_2805])).
% 5.75/2.18  tff(c_3334, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1329, c_3307])).
% 5.75/2.18  tff(c_3359, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_3334])).
% 5.75/2.18  tff(c_26, plain, (![A_24]: (k2_relat_1(k2_funct_1(A_24))=k1_relat_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.75/2.18  tff(c_18, plain, (![B_20, A_19]: (k5_relat_1(B_20, k6_relat_1(A_19))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.75/2.18  tff(c_208, plain, (![B_83, A_84]: (k5_relat_1(B_83, k6_partfun1(A_84))=B_83 | ~r1_tarski(k2_relat_1(B_83), A_84) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 5.75/2.18  tff(c_211, plain, (![A_24, A_84]: (k5_relat_1(k2_funct_1(A_24), k6_partfun1(A_84))=k2_funct_1(A_24) | ~r1_tarski(k1_relat_1(A_24), A_84) | ~v1_relat_1(k2_funct_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(superposition, [status(thm), theory('equality')], [c_26, c_208])).
% 5.75/2.18  tff(c_3404, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3359, c_211])).
% 5.75/2.18  tff(c_3425, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_76, c_60, c_987, c_3404])).
% 5.75/2.18  tff(c_3433, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3425])).
% 5.75/2.18  tff(c_3436, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_3433])).
% 5.75/2.18  tff(c_3440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_163, c_3436])).
% 5.75/2.18  tff(c_3441, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_3425])).
% 5.75/2.18  tff(c_16, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=B_18 | ~r1_tarski(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.75/2.18  tff(c_181, plain, (![A_77, B_78]: (k5_relat_1(k6_partfun1(A_77), B_78)=B_78 | ~r1_tarski(k1_relat_1(B_78), A_77) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_16])).
% 5.75/2.18  tff(c_185, plain, (![A_4, B_5]: (k5_relat_1(k6_partfun1(A_4), B_5)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_181])).
% 5.75/2.18  tff(c_3506, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3441, c_185])).
% 5.75/2.18  tff(c_3523, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_162, c_3506])).
% 5.75/2.18  tff(c_3525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_3523])).
% 5.75/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.18  
% 5.75/2.18  Inference rules
% 5.75/2.18  ----------------------
% 5.75/2.18  #Ref     : 0
% 5.75/2.18  #Sup     : 732
% 5.75/2.18  #Fact    : 0
% 5.75/2.18  #Define  : 0
% 5.75/2.18  #Split   : 5
% 5.75/2.18  #Chain   : 0
% 5.75/2.18  #Close   : 0
% 5.75/2.18  
% 5.75/2.18  Ordering : KBO
% 5.75/2.18  
% 5.75/2.18  Simplification rules
% 5.75/2.18  ----------------------
% 5.75/2.18  #Subsume      : 22
% 5.75/2.18  #Demod        : 738
% 5.75/2.18  #Tautology    : 264
% 5.75/2.18  #SimpNegUnit  : 2
% 5.75/2.18  #BackRed      : 27
% 5.75/2.18  
% 5.75/2.18  #Partial instantiations: 0
% 5.75/2.18  #Strategies tried      : 1
% 5.75/2.18  
% 5.75/2.18  Timing (in seconds)
% 5.75/2.18  ----------------------
% 5.75/2.19  Preprocessing        : 0.39
% 5.75/2.19  Parsing              : 0.21
% 5.75/2.19  CNF conversion       : 0.03
% 5.75/2.19  Main loop            : 0.97
% 5.75/2.19  Inferencing          : 0.34
% 5.75/2.19  Reduction            : 0.35
% 5.75/2.19  Demodulation         : 0.26
% 5.75/2.19  BG Simplification    : 0.04
% 5.75/2.19  Subsumption          : 0.18
% 5.75/2.19  Abstraction          : 0.04
% 5.75/2.19  MUC search           : 0.00
% 5.75/2.19  Cooper               : 0.00
% 5.75/2.19  Total                : 1.40
% 5.75/2.19  Index Insertion      : 0.00
% 5.75/2.19  Index Deletion       : 0.00
% 5.75/2.19  Index Matching       : 0.00
% 5.75/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
