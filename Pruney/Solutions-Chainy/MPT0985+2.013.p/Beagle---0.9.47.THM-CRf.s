%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:27 EST 2020

% Result     : Theorem 11.07s
% Output     : CNFRefutation 11.26s
% Verified   : 
% Statistics : Number of formulae       :  227 (1123 expanded)
%              Number of leaves         :   51 ( 386 expanded)
%              Depth                    :   14
%              Number of atoms          :  384 (3098 expanded)
%              Number of equality atoms :   98 ( 646 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_144,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_114,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_140,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_162,axiom,(
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

tff(f_172,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_184,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_relat_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_108,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_394,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_406,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_394])).

tff(c_112,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_106,plain,(
    v2_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_104,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_22943,plain,(
    ! [A_523,B_524,C_525] :
      ( k2_relset_1(A_523,B_524,C_525) = k2_relat_1(C_525)
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_22952,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_22943])).

tff(c_22966,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_22952])).

tff(c_62,plain,(
    ! [A_44] :
      ( k1_relat_1(k2_funct_1(A_44)) = k2_relat_1(A_44)
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_271,plain,(
    ! [A_81] :
      ( v1_funct_1(k2_funct_1(A_81))
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_102,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6')))
    | ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_198,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_274,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_271,c_198])).

tff(c_277,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_274])).

tff(c_291,plain,(
    ! [C_86,A_87,B_88] :
      ( v1_relat_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_294,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_291])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_294])).

tff(c_307,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_409,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_619,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_625,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_619])).

tff(c_638,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_625])).

tff(c_58,plain,(
    ! [A_43] :
      ( v1_relat_1(k2_funct_1(A_43))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_308,plain,(
    v1_funct_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_110,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_685,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_707,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_685])).

tff(c_6126,plain,(
    ! [B_270,A_271,C_272] :
      ( k1_xboole_0 = B_270
      | k1_relset_1(A_271,B_270,C_272) = A_271
      | ~ v1_funct_2(C_272,A_271,B_270)
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_271,B_270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_6138,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_108,c_6126])).

tff(c_6156,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_707,c_6138])).

tff(c_6160,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6156])).

tff(c_471,plain,(
    ! [A_111] :
      ( k2_relat_1(k2_funct_1(A_111)) = k1_relat_1(A_111)
      | ~ v2_funct_1(A_111)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92,plain,(
    ! [A_58] :
      ( v1_funct_2(A_58,k1_relat_1(A_58),k2_relat_1(A_58))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_18338,plain,(
    ! [A_422] :
      ( v1_funct_2(k2_funct_1(A_422),k1_relat_1(k2_funct_1(A_422)),k1_relat_1(A_422))
      | ~ v1_funct_1(k2_funct_1(A_422))
      | ~ v1_relat_1(k2_funct_1(A_422))
      | ~ v2_funct_1(A_422)
      | ~ v1_funct_1(A_422)
      | ~ v1_relat_1(A_422) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_92])).

tff(c_18341,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_6160,c_18338])).

tff(c_18358,plain,
    ( v1_funct_2(k2_funct_1('#skF_8'),k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')
    | ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_106,c_308,c_18341])).

tff(c_19290,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_18358])).

tff(c_19293,plain,
    ( ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_19290])).

tff(c_19297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_19293])).

tff(c_19299,plain,(
    v1_relat_1(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_18358])).

tff(c_60,plain,(
    ! [A_44] :
      ( k2_relat_1(k2_funct_1(A_44)) = k1_relat_1(A_44)
      | ~ v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_568,plain,(
    ! [A_119] :
      ( m1_subset_1(A_119,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_119),k2_relat_1(A_119))))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_21711,plain,(
    ! [A_452] :
      ( m1_subset_1(k2_funct_1(A_452),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_452)),k1_relat_1(A_452))))
      | ~ v1_funct_1(k2_funct_1(A_452))
      | ~ v1_relat_1(k2_funct_1(A_452))
      | ~ v2_funct_1(A_452)
      | ~ v1_funct_1(A_452)
      | ~ v1_relat_1(A_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_568])).

tff(c_21736,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')),'#skF_6')))
    | ~ v1_funct_1(k2_funct_1('#skF_8'))
    | ~ v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_6160,c_21711])).

tff(c_21761,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_106,c_19299,c_308,c_21736])).

tff(c_21792,plain,
    ( m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_8'),'#skF_6')))
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_21761])).

tff(c_21806,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_106,c_638,c_21792])).

tff(c_21808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_21806])).

tff(c_21809,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6156])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21852,plain,(
    ! [A_6] : r1_tarski('#skF_7',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21809,c_8])).

tff(c_188,plain,(
    ! [A_79] :
      ( v1_xboole_0(A_79)
      | r2_hidden('#skF_1'(A_79),A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_167,plain,(
    ! [A_70,B_71] : ~ r2_hidden(A_70,k2_zfmisc_1(A_70,B_71)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_197,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_188,c_170])).

tff(c_2736,plain,(
    ! [B_202,A_203] :
      ( m1_subset_1(B_202,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_202),A_203)))
      | ~ r1_tarski(k2_relat_1(B_202),A_203)
      | ~ v1_funct_1(B_202)
      | ~ v1_relat_1(B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_880,plain,(
    ! [A_151,C_152] :
      ( r2_hidden(k4_tarski('#skF_5'(A_151,k2_relat_1(A_151),C_152),C_152),A_151)
      | ~ r2_hidden(C_152,k2_relat_1(A_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_895,plain,(
    ! [C_152] :
      ( r2_hidden(k4_tarski('#skF_5'('#skF_8','#skF_7',C_152),C_152),'#skF_8')
      | ~ r2_hidden(C_152,k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_880])).

tff(c_1118,plain,(
    ! [C_163] :
      ( r2_hidden(k4_tarski('#skF_5'('#skF_8','#skF_7',C_163),C_163),'#skF_8')
      | ~ r2_hidden(C_163,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_895])).

tff(c_18,plain,(
    ! [C_14,A_11,B_12] :
      ( r2_hidden(C_14,A_11)
      | ~ r2_hidden(C_14,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1599,plain,(
    ! [C_176,A_177] :
      ( r2_hidden(k4_tarski('#skF_5'('#skF_8','#skF_7',C_176),C_176),A_177)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_177))
      | ~ r2_hidden(C_176,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1118,c_18])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1633,plain,(
    ! [A_177,C_176] :
      ( ~ v1_xboole_0(A_177)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_177))
      | ~ r2_hidden(C_176,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1599,c_2])).

tff(c_2135,plain,(
    ! [C_188] : ~ r2_hidden(C_188,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1633])).

tff(c_2150,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_2135])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2174,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2150,c_6])).

tff(c_2205,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2174,c_2174,c_12])).

tff(c_419,plain,(
    ! [A_102] :
      ( k4_relat_1(A_102) = k2_funct_1(A_102)
      | ~ v2_funct_1(A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_425,plain,
    ( k4_relat_1('#skF_8') = k2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_106,c_419])).

tff(c_429,plain,(
    k4_relat_1('#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_425])).

tff(c_38,plain,(
    ! [A_39] :
      ( v1_relat_1(k4_relat_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_439,plain,
    ( v1_relat_1(k2_funct_1('#skF_8'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_38])).

tff(c_447,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_439])).

tff(c_90,plain,(
    ! [A_58] :
      ( m1_subset_1(A_58,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_58),k2_relat_1(A_58))))
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_644,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_90])).

tff(c_651,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_644])).

tff(c_456,plain,(
    ! [C_107,A_108,B_109] :
      ( r2_hidden(C_107,A_108)
      | ~ r2_hidden(C_107,B_109)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_531,plain,(
    ! [A_114,A_115] :
      ( r2_hidden('#skF_1'(A_114),A_115)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(A_115))
      | v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_4,c_456])).

tff(c_546,plain,(
    ! [A_115,A_114] :
      ( ~ v1_xboole_0(A_115)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(A_115))
      | v1_xboole_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_531,c_2])).

tff(c_667,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_651,c_546])).

tff(c_677,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_667])).

tff(c_2478,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2205,c_677])).

tff(c_2485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2150,c_2478])).

tff(c_2486,plain,(
    ! [A_177] :
      ( ~ v1_xboole_0(A_177)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_177)) ) ),
    inference(splitRight,[status(thm)],[c_1633])).

tff(c_2740,plain,(
    ! [A_203] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'),A_203))
      | ~ r1_tarski(k2_relat_1('#skF_8'),A_203)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_2736,c_2486])).

tff(c_2775,plain,(
    ! [A_204] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'),A_204))
      | ~ r1_tarski('#skF_7',A_204) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_638,c_2740])).

tff(c_2779,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2775])).

tff(c_2781,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_2779])).

tff(c_21816,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21809,c_2781])).

tff(c_22198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21852,c_21816])).

tff(c_22200,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_439])).

tff(c_22241,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22200,c_6])).

tff(c_20,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22251,plain,(
    ! [A_15] : m1_subset_1('#skF_8',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22241,c_20])).

tff(c_154,plain,(
    ! [A_69] :
      ( v1_xboole_0(k4_relat_1(A_69))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_166,plain,(
    ! [A_69] :
      ( k4_relat_1(A_69) = k1_xboole_0
      | ~ v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_154,c_6])).

tff(c_22236,plain,(
    k4_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22200,c_166])).

tff(c_22284,plain,(
    k4_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22241,c_22236])).

tff(c_22285,plain,(
    k2_funct_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22284,c_429])).

tff(c_22308,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22285,c_409])).

tff(c_22426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22251,c_22308])).

tff(c_22427,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_22428,plain,(
    m1_subset_1(k2_funct_1('#skF_8'),k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_22850,plain,(
    ! [A_511,B_512,C_513] :
      ( k1_relset_1(A_511,B_512,C_513) = k1_relat_1(C_513)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_22867,plain,(
    k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) = k1_relat_1(k2_funct_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_22428,c_22850])).

tff(c_27852,plain,(
    ! [B_643,C_644,A_645] :
      ( k1_xboole_0 = B_643
      | v1_funct_2(C_644,A_645,B_643)
      | k1_relset_1(A_645,B_643,C_644) != A_645
      | ~ m1_subset_1(C_644,k1_zfmisc_1(k2_zfmisc_1(A_645,B_643))) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_27864,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relset_1('#skF_7','#skF_6',k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_22428,c_27852])).

tff(c_27884,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_funct_2(k2_funct_1('#skF_8'),'#skF_7','#skF_6')
    | k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22867,c_27864])).

tff(c_27885,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_22427,c_27884])).

tff(c_27891,plain,(
    k1_relat_1(k2_funct_1('#skF_8')) != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_27885])).

tff(c_27894,plain,
    ( k2_relat_1('#skF_8') != '#skF_7'
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_27891])).

tff(c_27897,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_106,c_22966,c_27894])).

tff(c_27898,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_27885])).

tff(c_27930,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27898,c_197])).

tff(c_27935,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27898,c_27898,c_12])).

tff(c_22442,plain,(
    ! [C_482,A_483,B_484] :
      ( r2_hidden(C_482,A_483)
      | ~ r2_hidden(C_482,B_484)
      | ~ m1_subset_1(B_484,k1_zfmisc_1(A_483)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22517,plain,(
    ! [A_493,A_494] :
      ( r2_hidden('#skF_1'(A_493),A_494)
      | ~ m1_subset_1(A_493,k1_zfmisc_1(A_494))
      | v1_xboole_0(A_493) ) ),
    inference(resolution,[status(thm)],[c_4,c_22442])).

tff(c_22547,plain,(
    ! [A_496,A_497] :
      ( ~ v1_xboole_0(A_496)
      | ~ m1_subset_1(A_497,k1_zfmisc_1(A_496))
      | v1_xboole_0(A_497) ) ),
    inference(resolution,[status(thm)],[c_22517,c_2])).

tff(c_22557,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6'))
    | v1_xboole_0(k2_funct_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_22428,c_22547])).

tff(c_22563,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_22557])).

tff(c_28293,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27935,c_22563])).

tff(c_28298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27930,c_28293])).

tff(c_28300,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_22557])).

tff(c_28419,plain,(
    k2_zfmisc_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28300,c_6])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | k2_zfmisc_1(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28476,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_28419,c_10])).

tff(c_28478,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_28476])).

tff(c_28492,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28478,c_197])).

tff(c_28497,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28478,c_28478,c_12])).

tff(c_22475,plain,(
    ! [A_491] :
      ( k4_relat_1(A_491) = k2_funct_1(A_491)
      | ~ v2_funct_1(A_491)
      | ~ v1_funct_1(A_491)
      | ~ v1_relat_1(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22481,plain,
    ( k4_relat_1('#skF_8') = k2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_106,c_22475])).

tff(c_22485,plain,(
    k4_relat_1('#skF_8') = k2_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_22481])).

tff(c_40,plain,(
    ! [A_39] :
      ( v1_xboole_0(k4_relat_1(A_39))
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22510,plain,
    ( v1_xboole_0(k2_funct_1('#skF_8'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_22485,c_40])).

tff(c_22516,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_22510])).

tff(c_22553,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_22547])).

tff(c_22560,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_22516,c_22553])).

tff(c_28700,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28497,c_22560])).

tff(c_28705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28492,c_28700])).

tff(c_28706,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28476])).

tff(c_28707,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_28476])).

tff(c_28739,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28706,c_28707])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28299,plain,(
    v1_xboole_0(k2_funct_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_22557])).

tff(c_28330,plain,(
    k2_funct_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28299,c_6])).

tff(c_28345,plain,
    ( k2_relat_1('#skF_8') = k1_relat_1(k1_xboole_0)
    | ~ v2_funct_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_28330,c_62])).

tff(c_28358,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_106,c_44,c_28345])).

tff(c_28710,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28706,c_28358])).

tff(c_28890,plain,(
    ! [A_670,B_671,C_672] :
      ( k2_relset_1(A_670,B_671,C_672) = k2_relat_1(C_672)
      | ~ m1_subset_1(C_672,k1_zfmisc_1(k2_zfmisc_1(A_670,B_671))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_28896,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_108,c_28890])).

tff(c_28899,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28710,c_104,c_28896])).

tff(c_28901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28739,c_28899])).

tff(c_28903,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_22510])).

tff(c_28921,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_28903,c_6])).

tff(c_28937,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28921,c_8])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28938,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28921,c_28921,c_42])).

tff(c_28936,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28921,c_28921,c_44])).

tff(c_29482,plain,(
    ! [B_724,A_725] :
      ( v1_funct_2(B_724,k1_relat_1(B_724),A_725)
      | ~ r1_tarski(k2_relat_1(B_724),A_725)
      | ~ v1_funct_1(B_724)
      | ~ v1_relat_1(B_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_29488,plain,(
    ! [A_725] :
      ( v1_funct_2('#skF_8','#skF_8',A_725)
      | ~ r1_tarski(k2_relat_1('#skF_8'),A_725)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28936,c_29482])).

tff(c_29494,plain,(
    ! [A_725] : v1_funct_2('#skF_8','#skF_8',A_725) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_112,c_28937,c_28938,c_29488])).

tff(c_28931,plain,(
    ! [A_15] : m1_subset_1('#skF_8',k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28921,c_20])).

tff(c_29153,plain,(
    ! [A_685,B_686,C_687] :
      ( k2_relset_1(A_685,B_686,C_687) = k2_relat_1(C_687)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(k2_zfmisc_1(A_685,B_686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_29157,plain,(
    ! [A_685,B_686] : k2_relset_1(A_685,B_686,'#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_28931,c_29153])).

tff(c_29165,plain,(
    ! [A_685,B_686] : k2_relset_1(A_685,B_686,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28938,c_29157])).

tff(c_29166,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29165,c_104])).

tff(c_321,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_197,c_166])).

tff(c_28926,plain,(
    k4_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28921,c_28921,c_321])).

tff(c_28984,plain,(
    k2_funct_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28926,c_22485])).

tff(c_29033,plain,(
    ~ v1_funct_2('#skF_8','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28984,c_22427])).

tff(c_29174,plain,(
    ~ v1_funct_2('#skF_8','#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29166,c_29033])).

tff(c_29498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29494,c_29174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:18:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.07/4.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.26/4.34  
% 11.26/4.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.26/4.34  %$ v1_funct_2 > v5_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_4
% 11.26/4.34  
% 11.26/4.34  %Foreground sorts:
% 11.26/4.34  
% 11.26/4.34  
% 11.26/4.34  %Background operators:
% 11.26/4.34  
% 11.26/4.34  
% 11.26/4.34  %Foreground operators:
% 11.26/4.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.26/4.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.26/4.34  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 11.26/4.34  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 11.26/4.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.26/4.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.26/4.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.26/4.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.26/4.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.26/4.34  tff('#skF_7', type, '#skF_7': $i).
% 11.26/4.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.26/4.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.26/4.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.26/4.34  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 11.26/4.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.26/4.34  tff('#skF_6', type, '#skF_6': $i).
% 11.26/4.34  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.26/4.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.26/4.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.26/4.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.26/4.34  tff('#skF_8', type, '#skF_8': $i).
% 11.26/4.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.26/4.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.26/4.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.26/4.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.26/4.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.26/4.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.26/4.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.26/4.34  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 11.26/4.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.26/4.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.26/4.34  
% 11.26/4.37  tff(f_201, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 11.26/4.37  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.26/4.37  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.26/4.37  tff(f_124, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 11.26/4.37  tff(f_114, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 11.26/4.37  tff(f_140, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.26/4.37  tff(f_162, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.26/4.37  tff(f_172, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 11.26/4.37  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.26/4.37  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.26/4.37  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.26/4.37  tff(f_46, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 11.26/4.37  tff(f_184, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 11.26/4.37  tff(f_73, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 11.26/4.37  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 11.26/4.37  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.26/4.37  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 11.26/4.37  tff(f_79, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_relat_1)).
% 11.26/4.37  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.26/4.37  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 11.26/4.37  tff(c_108, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.26/4.37  tff(c_394, plain, (![C_94, A_95, B_96]: (v1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.26/4.37  tff(c_406, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_108, c_394])).
% 11.26/4.37  tff(c_112, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.26/4.37  tff(c_106, plain, (v2_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.26/4.37  tff(c_104, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.26/4.37  tff(c_22943, plain, (![A_523, B_524, C_525]: (k2_relset_1(A_523, B_524, C_525)=k2_relat_1(C_525) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(A_523, B_524))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.26/4.37  tff(c_22952, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_108, c_22943])).
% 11.26/4.37  tff(c_22966, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_22952])).
% 11.26/4.37  tff(c_62, plain, (![A_44]: (k1_relat_1(k2_funct_1(A_44))=k2_relat_1(A_44) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.26/4.37  tff(c_271, plain, (![A_81]: (v1_funct_1(k2_funct_1(A_81)) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.26/4.37  tff(c_102, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6'))) | ~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.26/4.37  tff(c_198, plain, (~v1_funct_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_102])).
% 11.26/4.37  tff(c_274, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_271, c_198])).
% 11.26/4.37  tff(c_277, plain, (~v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_274])).
% 11.26/4.37  tff(c_291, plain, (![C_86, A_87, B_88]: (v1_relat_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.26/4.37  tff(c_294, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_108, c_291])).
% 11.26/4.37  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_294])).
% 11.26/4.37  tff(c_307, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | ~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_102])).
% 11.26/4.37  tff(c_409, plain, (~m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitLeft, [status(thm)], [c_307])).
% 11.26/4.37  tff(c_619, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.26/4.37  tff(c_625, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_108, c_619])).
% 11.26/4.37  tff(c_638, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_625])).
% 11.26/4.37  tff(c_58, plain, (![A_43]: (v1_relat_1(k2_funct_1(A_43)) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.26/4.37  tff(c_308, plain, (v1_funct_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_102])).
% 11.26/4.37  tff(c_110, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_201])).
% 11.26/4.37  tff(c_685, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.26/4.37  tff(c_707, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_108, c_685])).
% 11.26/4.37  tff(c_6126, plain, (![B_270, A_271, C_272]: (k1_xboole_0=B_270 | k1_relset_1(A_271, B_270, C_272)=A_271 | ~v1_funct_2(C_272, A_271, B_270) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_271, B_270))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 11.26/4.37  tff(c_6138, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_108, c_6126])).
% 11.26/4.37  tff(c_6156, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_707, c_6138])).
% 11.26/4.37  tff(c_6160, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_6156])).
% 11.26/4.37  tff(c_471, plain, (![A_111]: (k2_relat_1(k2_funct_1(A_111))=k1_relat_1(A_111) | ~v2_funct_1(A_111) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.26/4.37  tff(c_92, plain, (![A_58]: (v1_funct_2(A_58, k1_relat_1(A_58), k2_relat_1(A_58)) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_172])).
% 11.26/4.37  tff(c_18338, plain, (![A_422]: (v1_funct_2(k2_funct_1(A_422), k1_relat_1(k2_funct_1(A_422)), k1_relat_1(A_422)) | ~v1_funct_1(k2_funct_1(A_422)) | ~v1_relat_1(k2_funct_1(A_422)) | ~v2_funct_1(A_422) | ~v1_funct_1(A_422) | ~v1_relat_1(A_422))), inference(superposition, [status(thm), theory('equality')], [c_471, c_92])).
% 11.26/4.37  tff(c_18341, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_6') | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_6160, c_18338])).
% 11.26/4.37  tff(c_18358, plain, (v1_funct_2(k2_funct_1('#skF_8'), k1_relat_1(k2_funct_1('#skF_8')), '#skF_6') | ~v1_relat_1(k2_funct_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_106, c_308, c_18341])).
% 11.26/4.37  tff(c_19290, plain, (~v1_relat_1(k2_funct_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_18358])).
% 11.26/4.37  tff(c_19293, plain, (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_19290])).
% 11.26/4.37  tff(c_19297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_19293])).
% 11.26/4.37  tff(c_19299, plain, (v1_relat_1(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_18358])).
% 11.26/4.37  tff(c_60, plain, (![A_44]: (k2_relat_1(k2_funct_1(A_44))=k1_relat_1(A_44) | ~v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_124])).
% 11.26/4.37  tff(c_568, plain, (![A_119]: (m1_subset_1(A_119, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_119), k2_relat_1(A_119)))) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_172])).
% 11.26/4.37  tff(c_21711, plain, (![A_452]: (m1_subset_1(k2_funct_1(A_452), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_452)), k1_relat_1(A_452)))) | ~v1_funct_1(k2_funct_1(A_452)) | ~v1_relat_1(k2_funct_1(A_452)) | ~v2_funct_1(A_452) | ~v1_funct_1(A_452) | ~v1_relat_1(A_452))), inference(superposition, [status(thm), theory('equality')], [c_60, c_568])).
% 11.26/4.37  tff(c_21736, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')), '#skF_6'))) | ~v1_funct_1(k2_funct_1('#skF_8')) | ~v1_relat_1(k2_funct_1('#skF_8')) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_6160, c_21711])).
% 11.26/4.37  tff(c_21761, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_8')), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_106, c_19299, c_308, c_21736])).
% 11.26/4.37  tff(c_21792, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_8'), '#skF_6'))) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62, c_21761])).
% 11.26/4.37  tff(c_21806, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_106, c_638, c_21792])).
% 11.26/4.37  tff(c_21808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_21806])).
% 11.26/4.37  tff(c_21809, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6156])).
% 11.26/4.37  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.26/4.37  tff(c_21852, plain, (![A_6]: (r1_tarski('#skF_7', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_21809, c_8])).
% 11.26/4.37  tff(c_188, plain, (![A_79]: (v1_xboole_0(A_79) | r2_hidden('#skF_1'(A_79), A_79))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.26/4.37  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.26/4.37  tff(c_167, plain, (![A_70, B_71]: (~r2_hidden(A_70, k2_zfmisc_1(A_70, B_71)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.26/4.37  tff(c_170, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_167])).
% 11.26/4.37  tff(c_197, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_188, c_170])).
% 11.26/4.37  tff(c_2736, plain, (![B_202, A_203]: (m1_subset_1(B_202, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_202), A_203))) | ~r1_tarski(k2_relat_1(B_202), A_203) | ~v1_funct_1(B_202) | ~v1_relat_1(B_202))), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.26/4.37  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.26/4.37  tff(c_880, plain, (![A_151, C_152]: (r2_hidden(k4_tarski('#skF_5'(A_151, k2_relat_1(A_151), C_152), C_152), A_151) | ~r2_hidden(C_152, k2_relat_1(A_151)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.26/4.37  tff(c_895, plain, (![C_152]: (r2_hidden(k4_tarski('#skF_5'('#skF_8', '#skF_7', C_152), C_152), '#skF_8') | ~r2_hidden(C_152, k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_638, c_880])).
% 11.26/4.37  tff(c_1118, plain, (![C_163]: (r2_hidden(k4_tarski('#skF_5'('#skF_8', '#skF_7', C_163), C_163), '#skF_8') | ~r2_hidden(C_163, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_638, c_895])).
% 11.26/4.37  tff(c_18, plain, (![C_14, A_11, B_12]: (r2_hidden(C_14, A_11) | ~r2_hidden(C_14, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.26/4.37  tff(c_1599, plain, (![C_176, A_177]: (r2_hidden(k4_tarski('#skF_5'('#skF_8', '#skF_7', C_176), C_176), A_177) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_177)) | ~r2_hidden(C_176, '#skF_7'))), inference(resolution, [status(thm)], [c_1118, c_18])).
% 11.26/4.37  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.26/4.37  tff(c_1633, plain, (![A_177, C_176]: (~v1_xboole_0(A_177) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_177)) | ~r2_hidden(C_176, '#skF_7'))), inference(resolution, [status(thm)], [c_1599, c_2])).
% 11.26/4.37  tff(c_2135, plain, (![C_188]: (~r2_hidden(C_188, '#skF_7'))), inference(splitLeft, [status(thm)], [c_1633])).
% 11.26/4.37  tff(c_2150, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_2135])).
% 11.26/4.37  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.26/4.37  tff(c_2174, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2150, c_6])).
% 11.26/4.37  tff(c_2205, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2174, c_2174, c_12])).
% 11.26/4.37  tff(c_419, plain, (![A_102]: (k4_relat_1(A_102)=k2_funct_1(A_102) | ~v2_funct_1(A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.26/4.37  tff(c_425, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_106, c_419])).
% 11.26/4.37  tff(c_429, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_425])).
% 11.26/4.37  tff(c_38, plain, (![A_39]: (v1_relat_1(k4_relat_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.26/4.37  tff(c_439, plain, (v1_relat_1(k2_funct_1('#skF_8')) | ~v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_429, c_38])).
% 11.26/4.37  tff(c_447, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_439])).
% 11.26/4.37  tff(c_90, plain, (![A_58]: (m1_subset_1(A_58, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_58), k2_relat_1(A_58)))) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_172])).
% 11.26/4.37  tff(c_644, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_638, c_90])).
% 11.26/4.37  tff(c_651, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_644])).
% 11.26/4.37  tff(c_456, plain, (![C_107, A_108, B_109]: (r2_hidden(C_107, A_108) | ~r2_hidden(C_107, B_109) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.26/4.37  tff(c_531, plain, (![A_114, A_115]: (r2_hidden('#skF_1'(A_114), A_115) | ~m1_subset_1(A_114, k1_zfmisc_1(A_115)) | v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_4, c_456])).
% 11.26/4.37  tff(c_546, plain, (![A_115, A_114]: (~v1_xboole_0(A_115) | ~m1_subset_1(A_114, k1_zfmisc_1(A_115)) | v1_xboole_0(A_114))), inference(resolution, [status(thm)], [c_531, c_2])).
% 11.26/4.37  tff(c_667, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_651, c_546])).
% 11.26/4.37  tff(c_677, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_447, c_667])).
% 11.26/4.37  tff(c_2478, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2205, c_677])).
% 11.26/4.37  tff(c_2485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2150, c_2478])).
% 11.26/4.37  tff(c_2486, plain, (![A_177]: (~v1_xboole_0(A_177) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_177)))), inference(splitRight, [status(thm)], [c_1633])).
% 11.26/4.37  tff(c_2740, plain, (![A_203]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'), A_203)) | ~r1_tarski(k2_relat_1('#skF_8'), A_203) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_2736, c_2486])).
% 11.26/4.37  tff(c_2775, plain, (![A_204]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_8'), A_204)) | ~r1_tarski('#skF_7', A_204))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_638, c_2740])).
% 11.26/4.37  tff(c_2779, plain, (~v1_xboole_0(k1_xboole_0) | ~r1_tarski('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_2775])).
% 11.26/4.37  tff(c_2781, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_2779])).
% 11.26/4.37  tff(c_21816, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_21809, c_2781])).
% 11.26/4.37  tff(c_22198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21852, c_21816])).
% 11.26/4.37  tff(c_22200, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_439])).
% 11.26/4.37  tff(c_22241, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22200, c_6])).
% 11.26/4.37  tff(c_20, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.26/4.37  tff(c_22251, plain, (![A_15]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_22241, c_20])).
% 11.26/4.37  tff(c_154, plain, (![A_69]: (v1_xboole_0(k4_relat_1(A_69)) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.26/4.37  tff(c_166, plain, (![A_69]: (k4_relat_1(A_69)=k1_xboole_0 | ~v1_xboole_0(A_69))), inference(resolution, [status(thm)], [c_154, c_6])).
% 11.26/4.37  tff(c_22236, plain, (k4_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_22200, c_166])).
% 11.26/4.37  tff(c_22284, plain, (k4_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_22241, c_22236])).
% 11.26/4.37  tff(c_22285, plain, (k2_funct_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_22284, c_429])).
% 11.26/4.37  tff(c_22308, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_22285, c_409])).
% 11.26/4.37  tff(c_22426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22251, c_22308])).
% 11.26/4.37  tff(c_22427, plain, (~v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_307])).
% 11.26/4.37  tff(c_22428, plain, (m1_subset_1(k2_funct_1('#skF_8'), k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_6')))), inference(splitRight, [status(thm)], [c_307])).
% 11.26/4.37  tff(c_22850, plain, (![A_511, B_512, C_513]: (k1_relset_1(A_511, B_512, C_513)=k1_relat_1(C_513) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 11.26/4.37  tff(c_22867, plain, (k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))=k1_relat_1(k2_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_22428, c_22850])).
% 11.26/4.37  tff(c_27852, plain, (![B_643, C_644, A_645]: (k1_xboole_0=B_643 | v1_funct_2(C_644, A_645, B_643) | k1_relset_1(A_645, B_643, C_644)!=A_645 | ~m1_subset_1(C_644, k1_zfmisc_1(k2_zfmisc_1(A_645, B_643))))), inference(cnfTransformation, [status(thm)], [f_162])).
% 11.26/4.37  tff(c_27864, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relset_1('#skF_7', '#skF_6', k2_funct_1('#skF_8'))!='#skF_7'), inference(resolution, [status(thm)], [c_22428, c_27852])).
% 11.26/4.37  tff(c_27884, plain, (k1_xboole_0='#skF_6' | v1_funct_2(k2_funct_1('#skF_8'), '#skF_7', '#skF_6') | k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_22867, c_27864])).
% 11.26/4.37  tff(c_27885, plain, (k1_xboole_0='#skF_6' | k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_22427, c_27884])).
% 11.26/4.37  tff(c_27891, plain, (k1_relat_1(k2_funct_1('#skF_8'))!='#skF_7'), inference(splitLeft, [status(thm)], [c_27885])).
% 11.26/4.37  tff(c_27894, plain, (k2_relat_1('#skF_8')!='#skF_7' | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_62, c_27891])).
% 11.26/4.37  tff(c_27897, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_106, c_22966, c_27894])).
% 11.26/4.37  tff(c_27898, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_27885])).
% 11.26/4.37  tff(c_27930, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27898, c_197])).
% 11.26/4.37  tff(c_27935, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27898, c_27898, c_12])).
% 11.26/4.37  tff(c_22442, plain, (![C_482, A_483, B_484]: (r2_hidden(C_482, A_483) | ~r2_hidden(C_482, B_484) | ~m1_subset_1(B_484, k1_zfmisc_1(A_483)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.26/4.37  tff(c_22517, plain, (![A_493, A_494]: (r2_hidden('#skF_1'(A_493), A_494) | ~m1_subset_1(A_493, k1_zfmisc_1(A_494)) | v1_xboole_0(A_493))), inference(resolution, [status(thm)], [c_4, c_22442])).
% 11.26/4.37  tff(c_22547, plain, (![A_496, A_497]: (~v1_xboole_0(A_496) | ~m1_subset_1(A_497, k1_zfmisc_1(A_496)) | v1_xboole_0(A_497))), inference(resolution, [status(thm)], [c_22517, c_2])).
% 11.26/4.37  tff(c_22557, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6')) | v1_xboole_0(k2_funct_1('#skF_8'))), inference(resolution, [status(thm)], [c_22428, c_22547])).
% 11.26/4.37  tff(c_22563, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_22557])).
% 11.26/4.37  tff(c_28293, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27935, c_22563])).
% 11.26/4.37  tff(c_28298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27930, c_28293])).
% 11.26/4.37  tff(c_28300, plain, (v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_22557])).
% 11.26/4.37  tff(c_28419, plain, (k2_zfmisc_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_28300, c_6])).
% 11.26/4.37  tff(c_10, plain, (![B_8, A_7]: (k1_xboole_0=B_8 | k1_xboole_0=A_7 | k2_zfmisc_1(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.26/4.37  tff(c_28476, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_28419, c_10])).
% 11.26/4.37  tff(c_28478, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_28476])).
% 11.26/4.37  tff(c_28492, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28478, c_197])).
% 11.26/4.37  tff(c_28497, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28478, c_28478, c_12])).
% 11.26/4.37  tff(c_22475, plain, (![A_491]: (k4_relat_1(A_491)=k2_funct_1(A_491) | ~v2_funct_1(A_491) | ~v1_funct_1(A_491) | ~v1_relat_1(A_491))), inference(cnfTransformation, [status(thm)], [f_106])).
% 11.26/4.37  tff(c_22481, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_106, c_22475])).
% 11.26/4.37  tff(c_22485, plain, (k4_relat_1('#skF_8')=k2_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_22481])).
% 11.26/4.37  tff(c_40, plain, (![A_39]: (v1_xboole_0(k4_relat_1(A_39)) | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.26/4.37  tff(c_22510, plain, (v1_xboole_0(k2_funct_1('#skF_8')) | ~v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_22485, c_40])).
% 11.26/4.37  tff(c_22516, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_22510])).
% 11.26/4.37  tff(c_22553, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_108, c_22547])).
% 11.26/4.37  tff(c_22560, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_22516, c_22553])).
% 11.26/4.37  tff(c_28700, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_28497, c_22560])).
% 11.26/4.37  tff(c_28705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28492, c_28700])).
% 11.26/4.37  tff(c_28706, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_28476])).
% 11.26/4.37  tff(c_28707, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_28476])).
% 11.26/4.37  tff(c_28739, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28706, c_28707])).
% 11.26/4.37  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.26/4.37  tff(c_28299, plain, (v1_xboole_0(k2_funct_1('#skF_8'))), inference(splitRight, [status(thm)], [c_22557])).
% 11.26/4.37  tff(c_28330, plain, (k2_funct_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_28299, c_6])).
% 11.26/4.37  tff(c_28345, plain, (k2_relat_1('#skF_8')=k1_relat_1(k1_xboole_0) | ~v2_funct_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_28330, c_62])).
% 11.26/4.37  tff(c_28358, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_106, c_44, c_28345])).
% 11.26/4.37  tff(c_28710, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28706, c_28358])).
% 11.26/4.37  tff(c_28890, plain, (![A_670, B_671, C_672]: (k2_relset_1(A_670, B_671, C_672)=k2_relat_1(C_672) | ~m1_subset_1(C_672, k1_zfmisc_1(k2_zfmisc_1(A_670, B_671))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.26/4.37  tff(c_28896, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_108, c_28890])).
% 11.26/4.37  tff(c_28899, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28710, c_104, c_28896])).
% 11.26/4.37  tff(c_28901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28739, c_28899])).
% 11.26/4.37  tff(c_28903, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_22510])).
% 11.26/4.37  tff(c_28921, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_28903, c_6])).
% 11.26/4.37  tff(c_28937, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_28921, c_8])).
% 11.26/4.37  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.26/4.37  tff(c_28938, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28921, c_28921, c_42])).
% 11.26/4.37  tff(c_28936, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28921, c_28921, c_44])).
% 11.26/4.37  tff(c_29482, plain, (![B_724, A_725]: (v1_funct_2(B_724, k1_relat_1(B_724), A_725) | ~r1_tarski(k2_relat_1(B_724), A_725) | ~v1_funct_1(B_724) | ~v1_relat_1(B_724))), inference(cnfTransformation, [status(thm)], [f_184])).
% 11.26/4.37  tff(c_29488, plain, (![A_725]: (v1_funct_2('#skF_8', '#skF_8', A_725) | ~r1_tarski(k2_relat_1('#skF_8'), A_725) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_28936, c_29482])).
% 11.26/4.37  tff(c_29494, plain, (![A_725]: (v1_funct_2('#skF_8', '#skF_8', A_725))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_112, c_28937, c_28938, c_29488])).
% 11.26/4.37  tff(c_28931, plain, (![A_15]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_28921, c_20])).
% 11.26/4.37  tff(c_29153, plain, (![A_685, B_686, C_687]: (k2_relset_1(A_685, B_686, C_687)=k2_relat_1(C_687) | ~m1_subset_1(C_687, k1_zfmisc_1(k2_zfmisc_1(A_685, B_686))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.26/4.37  tff(c_29157, plain, (![A_685, B_686]: (k2_relset_1(A_685, B_686, '#skF_8')=k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_28931, c_29153])).
% 11.26/4.37  tff(c_29165, plain, (![A_685, B_686]: (k2_relset_1(A_685, B_686, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28938, c_29157])).
% 11.26/4.37  tff(c_29166, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_29165, c_104])).
% 11.26/4.37  tff(c_321, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_197, c_166])).
% 11.26/4.37  tff(c_28926, plain, (k4_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28921, c_28921, c_321])).
% 11.26/4.37  tff(c_28984, plain, (k2_funct_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_28926, c_22485])).
% 11.26/4.37  tff(c_29033, plain, (~v1_funct_2('#skF_8', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28984, c_22427])).
% 11.26/4.37  tff(c_29174, plain, (~v1_funct_2('#skF_8', '#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29166, c_29033])).
% 11.26/4.37  tff(c_29498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29494, c_29174])).
% 11.26/4.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.26/4.37  
% 11.26/4.37  Inference rules
% 11.26/4.37  ----------------------
% 11.26/4.37  #Ref     : 0
% 11.26/4.37  #Sup     : 7383
% 11.26/4.37  #Fact    : 0
% 11.26/4.37  #Define  : 0
% 11.26/4.37  #Split   : 41
% 11.26/4.37  #Chain   : 0
% 11.26/4.37  #Close   : 0
% 11.26/4.37  
% 11.26/4.37  Ordering : KBO
% 11.26/4.37  
% 11.26/4.37  Simplification rules
% 11.26/4.37  ----------------------
% 11.26/4.37  #Subsume      : 1929
% 11.26/4.37  #Demod        : 8757
% 11.26/4.37  #Tautology    : 2896
% 11.26/4.37  #SimpNegUnit  : 71
% 11.26/4.37  #BackRed      : 854
% 11.26/4.37  
% 11.26/4.37  #Partial instantiations: 0
% 11.26/4.37  #Strategies tried      : 1
% 11.26/4.37  
% 11.26/4.37  Timing (in seconds)
% 11.26/4.37  ----------------------
% 11.26/4.37  Preprocessing        : 0.37
% 11.26/4.37  Parsing              : 0.20
% 11.26/4.37  CNF conversion       : 0.03
% 11.26/4.37  Main loop            : 3.24
% 11.26/4.37  Inferencing          : 0.76
% 11.26/4.37  Reduction            : 1.04
% 11.26/4.37  Demodulation         : 0.77
% 11.26/4.37  BG Simplification    : 0.10
% 11.26/4.37  Subsumption          : 1.14
% 11.26/4.37  Abstraction          : 0.12
% 11.26/4.37  MUC search           : 0.00
% 11.26/4.37  Cooper               : 0.00
% 11.26/4.37  Total                : 3.68
% 11.26/4.37  Index Insertion      : 0.00
% 11.26/4.37  Index Deletion       : 0.00
% 11.26/4.37  Index Matching       : 0.00
% 11.26/4.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
