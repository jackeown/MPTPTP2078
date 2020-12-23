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
% DateTime   : Thu Dec  3 10:17:00 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 406 expanded)
%              Number of leaves         :   29 ( 155 expanded)
%              Depth                    :   12
%              Number of atoms          :  224 (1295 expanded)
%              Number of equality atoms :   59 ( 345 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
            <=> ! [D] :
                  ( r2_hidden(D,k1_relset_1(A,A,B))
                 => k1_funct_1(B,D) = k1_funct_1(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_2)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
           => ( r1_partfun1(A,B)
            <=> ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_partfun1)).

tff(c_44,plain,
    ( r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3'))
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_63,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_69,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_82,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_69])).

tff(c_85,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_78])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_99,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_99])).

tff(c_141,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k1_relset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_157,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_141])).

tff(c_164,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_157])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_195,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_164,c_2])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_112,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_99])).

tff(c_311,plain,(
    ! [B_79,A_80,C_81] :
      ( k1_xboole_0 = B_79
      | k1_relset_1(A_80,B_79,C_81) = A_80
      | ~ v1_funct_2(C_81,A_80,B_79)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_325,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_311])).

tff(c_332,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112,c_325])).

tff(c_333,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_332])).

tff(c_420,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_1'(A_90,B_91),k1_relat_1(A_90))
      | r1_partfun1(A_90,B_91)
      | ~ r1_tarski(k1_relat_1(A_90),k1_relat_1(B_91))
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    ! [D_34] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_34) = k1_funct_1('#skF_4',D_34)
      | ~ r2_hidden(D_34,k1_relset_1('#skF_2','#skF_2','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_117,plain,(
    ! [D_34] :
      ( r1_partfun1('#skF_3','#skF_4')
      | k1_funct_1('#skF_3',D_34) = k1_funct_1('#skF_4',D_34)
      | ~ r2_hidden(D_34,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_52])).

tff(c_118,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_3',D_34) = k1_funct_1('#skF_4',D_34)
      | ~ r2_hidden(D_34,k1_relat_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_117])).

tff(c_424,plain,(
    ! [B_91] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_91)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_91))
      | r1_partfun1('#skF_3',B_91)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_91))
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_420,c_118])).

tff(c_518,plain,(
    ! [B_111] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_111)) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_111))
      | r1_partfun1('#skF_3',B_111)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_111))
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_40,c_424])).

tff(c_521,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_518])).

tff(c_523,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_36,c_195,c_521])).

tff(c_524,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_523])).

tff(c_28,plain,(
    ! [B_23,A_17] :
      ( k1_funct_1(B_23,'#skF_1'(A_17,B_23)) != k1_funct_1(A_17,'#skF_1'(A_17,B_23))
      | r1_partfun1(A_17,B_23)
      | ~ r1_tarski(k1_relat_1(A_17),k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_527,plain,
    ( r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_28])).

tff(c_532,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_40,c_85,c_36,c_195,c_333,c_527])).

tff(c_534,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_532])).

tff(c_536,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_54,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_535,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_332])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_300,plain,(
    ! [B_77,C_78] :
      ( k1_relset_1(k1_xboole_0,B_77,C_78) = k1_xboole_0
      | ~ v1_funct_2(C_78,k1_xboole_0,B_77)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_310,plain,(
    ! [B_77,A_1] :
      ( k1_relset_1(k1_xboole_0,B_77,A_1) = k1_xboole_0
      | ~ v1_funct_2(A_1,k1_xboole_0,B_77)
      | ~ r1_tarski(A_1,k2_zfmisc_1(k1_xboole_0,B_77)) ) ),
    inference(resolution,[status(thm)],[c_4,c_300])).

tff(c_598,plain,(
    ! [B_119,A_120] :
      ( k1_relset_1('#skF_2',B_119,A_120) = '#skF_2'
      | ~ v1_funct_2(A_120,'#skF_2',B_119)
      | ~ r1_tarski(A_120,k2_zfmisc_1('#skF_2',B_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_535,c_535,c_535,c_310])).

tff(c_605,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_598])).

tff(c_612,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112,c_605])).

tff(c_614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_612])).

tff(c_616,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,
    ( k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_617,plain,(
    ~ r1_partfun1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_617])).

tff(c_620,plain,(
    k1_funct_1('#skF_3','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_628,plain,(
    ! [B_123,A_124] :
      ( v1_relat_1(B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_124))
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_637,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_628])).

tff(c_644,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_637])).

tff(c_665,plain,(
    ! [A_129,B_130,C_131] :
      ( k1_relset_1(A_129,B_130,C_131) = k1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_677,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_665])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k1_relset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_697,plain,
    ( m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_10])).

tff(c_701,plain,(
    m1_subset_1(k1_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_697])).

tff(c_710,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_701,c_2])).

tff(c_678,plain,(
    k1_relset_1('#skF_2','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_665])).

tff(c_875,plain,(
    ! [B_162,A_163,C_164] :
      ( k1_xboole_0 = B_162
      | k1_relset_1(A_163,B_162,C_164) = A_163
      | ~ v1_funct_2(C_164,A_163,B_162)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_163,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_889,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_875])).

tff(c_896,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_678,c_889])).

tff(c_897,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_896])).

tff(c_634,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_628])).

tff(c_641,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_634])).

tff(c_615,plain,(
    r2_hidden('#skF_5',k1_relset_1('#skF_2','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_693,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_615])).

tff(c_1087,plain,(
    ! [B_203,C_204,A_205] :
      ( k1_funct_1(B_203,C_204) = k1_funct_1(A_205,C_204)
      | ~ r2_hidden(C_204,k1_relat_1(A_205))
      | ~ r1_partfun1(A_205,B_203)
      | ~ r1_tarski(k1_relat_1(A_205),k1_relat_1(B_203))
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203)
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1093,plain,(
    ! [B_203] :
      ( k1_funct_1(B_203,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_203)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_203))
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_693,c_1087])).

tff(c_1100,plain,(
    ! [B_206] :
      ( k1_funct_1(B_206,'#skF_5') = k1_funct_1('#skF_3','#skF_5')
      | ~ r1_partfun1('#skF_3',B_206)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_206))
      | ~ v1_funct_1(B_206)
      | ~ v1_relat_1(B_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_40,c_1093])).

tff(c_1103,plain,
    ( k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ r1_partfun1('#skF_3','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_1100])).

tff(c_1105,plain,(
    k1_funct_1('#skF_3','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_36,c_710,c_616,c_1103])).

tff(c_1107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_1105])).

tff(c_1109,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_896])).

tff(c_1108,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_896])).

tff(c_858,plain,(
    ! [B_158,C_159] :
      ( k1_relset_1(k1_xboole_0,B_158,C_159) = k1_xboole_0
      | ~ v1_funct_2(C_159,k1_xboole_0,B_158)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_868,plain,(
    ! [B_158,A_1] :
      ( k1_relset_1(k1_xboole_0,B_158,A_1) = k1_xboole_0
      | ~ v1_funct_2(A_1,k1_xboole_0,B_158)
      | ~ r1_tarski(A_1,k2_zfmisc_1(k1_xboole_0,B_158)) ) ),
    inference(resolution,[status(thm)],[c_4,c_858])).

tff(c_1211,plain,(
    ! [B_218,A_219] :
      ( k1_relset_1('#skF_2',B_218,A_219) = '#skF_2'
      | ~ v1_funct_2(A_219,'#skF_2',B_218)
      | ~ r1_tarski(A_219,k2_zfmisc_1('#skF_2',B_218)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_1108,c_1108,c_1108,c_868])).

tff(c_1218,plain,
    ( k1_relset_1('#skF_2','#skF_2','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1211])).

tff(c_1225,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_678,c_1218])).

tff(c_1227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1109,c_1225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:06:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.60  
% 3.50/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.60  %$ v1_funct_2 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.50/1.60  
% 3.50/1.60  %Foreground sorts:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Background operators:
% 3.50/1.60  
% 3.50/1.60  
% 3.50/1.60  %Foreground operators:
% 3.50/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.50/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.50/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.50/1.60  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.50/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.60  
% 3.50/1.62  tff(f_101, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) <=> (![D]: (r2_hidden(D, k1_relset_1(A, A, B)) => (k1_funct_1(B, D) = k1_funct_1(C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_2)).
% 3.50/1.62  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.50/1.62  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.50/1.62  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.50/1.62  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.50/1.62  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.50/1.62  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.50/1.62  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) => (r1_partfun1(A, B) <=> (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_partfun1)).
% 3.50/1.62  tff(c_44, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3')) | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_63, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 3.50/1.62  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.50/1.62  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_69, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.50/1.62  tff(c_75, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_69])).
% 3.50/1.62  tff(c_82, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_75])).
% 3.50/1.62  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_78, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_69])).
% 3.50/1.62  tff(c_85, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_78])).
% 3.50/1.62  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_99, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.50/1.62  tff(c_111, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_99])).
% 3.50/1.62  tff(c_141, plain, (![A_54, B_55, C_56]: (m1_subset_1(k1_relset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.62  tff(c_157, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_141])).
% 3.50/1.62  tff(c_164, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_157])).
% 3.50/1.62  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.62  tff(c_195, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_164, c_2])).
% 3.50/1.62  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_112, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_99])).
% 3.50/1.62  tff(c_311, plain, (![B_79, A_80, C_81]: (k1_xboole_0=B_79 | k1_relset_1(A_80, B_79, C_81)=A_80 | ~v1_funct_2(C_81, A_80, B_79) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.62  tff(c_325, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_311])).
% 3.50/1.62  tff(c_332, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_112, c_325])).
% 3.50/1.62  tff(c_333, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_332])).
% 3.50/1.62  tff(c_420, plain, (![A_90, B_91]: (r2_hidden('#skF_1'(A_90, B_91), k1_relat_1(A_90)) | r1_partfun1(A_90, B_91) | ~r1_tarski(k1_relat_1(A_90), k1_relat_1(B_91)) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.50/1.62  tff(c_52, plain, (![D_34]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_34)=k1_funct_1('#skF_4', D_34) | ~r2_hidden(D_34, k1_relset_1('#skF_2', '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_117, plain, (![D_34]: (r1_partfun1('#skF_3', '#skF_4') | k1_funct_1('#skF_3', D_34)=k1_funct_1('#skF_4', D_34) | ~r2_hidden(D_34, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_52])).
% 3.50/1.62  tff(c_118, plain, (![D_34]: (k1_funct_1('#skF_3', D_34)=k1_funct_1('#skF_4', D_34) | ~r2_hidden(D_34, k1_relat_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_63, c_117])).
% 3.50/1.62  tff(c_424, plain, (![B_91]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_91))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_91)) | r1_partfun1('#skF_3', B_91) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_91)) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_420, c_118])).
% 3.50/1.62  tff(c_518, plain, (![B_111]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_111))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_111)) | r1_partfun1('#skF_3', B_111) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_111)) | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_40, c_424])).
% 3.50/1.62  tff(c_521, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_333, c_518])).
% 3.50/1.62  tff(c_523, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_36, c_195, c_521])).
% 3.50/1.62  tff(c_524, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_63, c_523])).
% 3.50/1.62  tff(c_28, plain, (![B_23, A_17]: (k1_funct_1(B_23, '#skF_1'(A_17, B_23))!=k1_funct_1(A_17, '#skF_1'(A_17, B_23)) | r1_partfun1(A_17, B_23) | ~r1_tarski(k1_relat_1(A_17), k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.50/1.62  tff(c_527, plain, (r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_524, c_28])).
% 3.50/1.62  tff(c_532, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_40, c_85, c_36, c_195, c_333, c_527])).
% 3.50/1.62  tff(c_534, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_532])).
% 3.50/1.62  tff(c_536, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_332])).
% 3.50/1.62  tff(c_54, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.62  tff(c_62, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_54])).
% 3.50/1.62  tff(c_535, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_332])).
% 3.50/1.62  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.62  tff(c_300, plain, (![B_77, C_78]: (k1_relset_1(k1_xboole_0, B_77, C_78)=k1_xboole_0 | ~v1_funct_2(C_78, k1_xboole_0, B_77) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_77))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.62  tff(c_310, plain, (![B_77, A_1]: (k1_relset_1(k1_xboole_0, B_77, A_1)=k1_xboole_0 | ~v1_funct_2(A_1, k1_xboole_0, B_77) | ~r1_tarski(A_1, k2_zfmisc_1(k1_xboole_0, B_77)))), inference(resolution, [status(thm)], [c_4, c_300])).
% 3.50/1.62  tff(c_598, plain, (![B_119, A_120]: (k1_relset_1('#skF_2', B_119, A_120)='#skF_2' | ~v1_funct_2(A_120, '#skF_2', B_119) | ~r1_tarski(A_120, k2_zfmisc_1('#skF_2', B_119)))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_535, c_535, c_535, c_310])).
% 3.50/1.62  tff(c_605, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_598])).
% 3.50/1.62  tff(c_612, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_112, c_605])).
% 3.50/1.62  tff(c_614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_536, c_612])).
% 3.50/1.62  tff(c_616, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 3.50/1.62  tff(c_42, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.62  tff(c_617, plain, (~r1_partfun1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 3.50/1.62  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_616, c_617])).
% 3.50/1.62  tff(c_620, plain, (k1_funct_1('#skF_3', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 3.50/1.62  tff(c_628, plain, (![B_123, A_124]: (v1_relat_1(B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(A_124)) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.50/1.62  tff(c_637, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_628])).
% 3.50/1.62  tff(c_644, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_637])).
% 3.50/1.62  tff(c_665, plain, (![A_129, B_130, C_131]: (k1_relset_1(A_129, B_130, C_131)=k1_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.50/1.62  tff(c_677, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_665])).
% 3.50/1.62  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k1_relset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.62  tff(c_697, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_677, c_10])).
% 3.50/1.62  tff(c_701, plain, (m1_subset_1(k1_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_697])).
% 3.50/1.62  tff(c_710, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_701, c_2])).
% 3.50/1.62  tff(c_678, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_665])).
% 3.50/1.62  tff(c_875, plain, (![B_162, A_163, C_164]: (k1_xboole_0=B_162 | k1_relset_1(A_163, B_162, C_164)=A_163 | ~v1_funct_2(C_164, A_163, B_162) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_163, B_162))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.62  tff(c_889, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_875])).
% 3.50/1.62  tff(c_896, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_678, c_889])).
% 3.50/1.62  tff(c_897, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_896])).
% 3.50/1.62  tff(c_634, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_628])).
% 3.50/1.62  tff(c_641, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_634])).
% 3.50/1.62  tff(c_615, plain, (r2_hidden('#skF_5', k1_relset_1('#skF_2', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 3.50/1.62  tff(c_693, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_677, c_615])).
% 3.50/1.62  tff(c_1087, plain, (![B_203, C_204, A_205]: (k1_funct_1(B_203, C_204)=k1_funct_1(A_205, C_204) | ~r2_hidden(C_204, k1_relat_1(A_205)) | ~r1_partfun1(A_205, B_203) | ~r1_tarski(k1_relat_1(A_205), k1_relat_1(B_203)) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.50/1.62  tff(c_1093, plain, (![B_203]: (k1_funct_1(B_203, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_203) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_203)) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_693, c_1087])).
% 3.50/1.62  tff(c_1100, plain, (![B_206]: (k1_funct_1(B_206, '#skF_5')=k1_funct_1('#skF_3', '#skF_5') | ~r1_partfun1('#skF_3', B_206) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_206)) | ~v1_funct_1(B_206) | ~v1_relat_1(B_206))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_40, c_1093])).
% 3.50/1.62  tff(c_1103, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~r1_partfun1('#skF_3', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_897, c_1100])).
% 3.50/1.62  tff(c_1105, plain, (k1_funct_1('#skF_3', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_644, c_36, c_710, c_616, c_1103])).
% 3.50/1.62  tff(c_1107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_1105])).
% 3.50/1.62  tff(c_1109, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitRight, [status(thm)], [c_896])).
% 3.50/1.62  tff(c_1108, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_896])).
% 3.50/1.62  tff(c_858, plain, (![B_158, C_159]: (k1_relset_1(k1_xboole_0, B_158, C_159)=k1_xboole_0 | ~v1_funct_2(C_159, k1_xboole_0, B_158) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_158))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.62  tff(c_868, plain, (![B_158, A_1]: (k1_relset_1(k1_xboole_0, B_158, A_1)=k1_xboole_0 | ~v1_funct_2(A_1, k1_xboole_0, B_158) | ~r1_tarski(A_1, k2_zfmisc_1(k1_xboole_0, B_158)))), inference(resolution, [status(thm)], [c_4, c_858])).
% 3.50/1.62  tff(c_1211, plain, (![B_218, A_219]: (k1_relset_1('#skF_2', B_218, A_219)='#skF_2' | ~v1_funct_2(A_219, '#skF_2', B_218) | ~r1_tarski(A_219, k2_zfmisc_1('#skF_2', B_218)))), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_1108, c_1108, c_1108, c_868])).
% 3.50/1.62  tff(c_1218, plain, (k1_relset_1('#skF_2', '#skF_2', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_1211])).
% 3.50/1.62  tff(c_1225, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_678, c_1218])).
% 3.50/1.62  tff(c_1227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1109, c_1225])).
% 3.50/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.62  
% 3.50/1.62  Inference rules
% 3.50/1.62  ----------------------
% 3.50/1.62  #Ref     : 2
% 3.50/1.62  #Sup     : 222
% 3.50/1.62  #Fact    : 0
% 3.50/1.62  #Define  : 0
% 3.50/1.62  #Split   : 11
% 3.50/1.62  #Chain   : 0
% 3.50/1.62  #Close   : 0
% 3.50/1.62  
% 3.50/1.62  Ordering : KBO
% 3.50/1.62  
% 3.50/1.62  Simplification rules
% 3.50/1.62  ----------------------
% 3.50/1.62  #Subsume      : 38
% 3.50/1.62  #Demod        : 238
% 3.50/1.62  #Tautology    : 67
% 3.50/1.62  #SimpNegUnit  : 16
% 3.50/1.62  #BackRed      : 24
% 3.50/1.62  
% 3.50/1.62  #Partial instantiations: 0
% 3.50/1.62  #Strategies tried      : 1
% 3.50/1.62  
% 3.50/1.62  Timing (in seconds)
% 3.50/1.62  ----------------------
% 3.50/1.62  Preprocessing        : 0.34
% 3.50/1.62  Parsing              : 0.18
% 3.50/1.62  CNF conversion       : 0.02
% 3.50/1.62  Main loop            : 0.46
% 3.50/1.62  Inferencing          : 0.18
% 3.50/1.62  Reduction            : 0.14
% 3.50/1.62  Demodulation         : 0.10
% 3.50/1.62  BG Simplification    : 0.03
% 3.50/1.62  Subsumption          : 0.08
% 3.50/1.62  Abstraction          : 0.03
% 3.50/1.62  MUC search           : 0.00
% 3.50/1.62  Cooper               : 0.00
% 3.50/1.62  Total                : 0.85
% 3.50/1.62  Index Insertion      : 0.00
% 3.50/1.62  Index Deletion       : 0.00
% 3.50/1.62  Index Matching       : 0.00
% 3.50/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
