%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:43 EST 2020

% Result     : Theorem 12.95s
% Output     : CNFRefutation 13.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 318 expanded)
%              Number of leaves         :   40 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  165 ( 743 expanded)
%              Number of equality atoms :   52 ( 174 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_112,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_41008,plain,(
    ! [A_802] :
      ( r1_tarski(A_802,k2_zfmisc_1(k1_relat_1(A_802),k2_relat_1(A_802)))
      | ~ v1_relat_1(A_802) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40911,plain,(
    ! [A_788,B_789] :
      ( m1_subset_1(A_788,k1_zfmisc_1(B_789))
      | ~ r1_tarski(A_788,B_789) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17)))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_459,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5263,plain,(
    ! [A_267,B_268,A_269] :
      ( k1_relset_1(A_267,B_268,A_269) = k1_relat_1(A_269)
      | ~ r1_tarski(A_269,k2_zfmisc_1(A_267,B_268)) ) ),
    inference(resolution,[status(thm)],[c_20,c_459])).

tff(c_5311,plain,(
    ! [A_17] :
      ( k1_relset_1(k1_relat_1(A_17),k2_relat_1(A_17),A_17) = k1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_5263])).

tff(c_1192,plain,(
    ! [B_162,C_163,A_164] :
      ( k1_xboole_0 = B_162
      | v1_funct_2(C_163,A_164,B_162)
      | k1_relset_1(A_164,B_162,C_163) != A_164
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_10777,plain,(
    ! [B_393,A_394,A_395] :
      ( k1_xboole_0 = B_393
      | v1_funct_2(A_394,A_395,B_393)
      | k1_relset_1(A_395,B_393,A_394) != A_395
      | ~ r1_tarski(A_394,k2_zfmisc_1(A_395,B_393)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1192])).

tff(c_40013,plain,(
    ! [A_768] :
      ( k2_relat_1(A_768) = k1_xboole_0
      | v1_funct_2(A_768,k1_relat_1(A_768),k2_relat_1(A_768))
      | k1_relset_1(k1_relat_1(A_768),k2_relat_1(A_768),A_768) != k1_relat_1(A_768)
      | ~ v1_relat_1(A_768) ) ),
    inference(resolution,[status(thm)],[c_26,c_10777])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62])).

tff(c_121,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_40020,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40013,c_121])).

tff(c_40083,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40020])).

tff(c_40122,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'),'#skF_4') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40083])).

tff(c_40125,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5311,c_40122])).

tff(c_40129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_40125])).

tff(c_40130,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40083])).

tff(c_273,plain,(
    ! [C_84,B_85,A_86] :
      ( v1_xboole_0(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(B_85,A_86)))
      | ~ v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_506,plain,(
    ! [A_110,A_111,B_112] :
      ( v1_xboole_0(A_110)
      | ~ v1_xboole_0(A_111)
      | ~ r1_tarski(A_110,k2_zfmisc_1(B_112,A_111)) ) ),
    inference(resolution,[status(thm)],[c_20,c_273])).

tff(c_523,plain,(
    ! [A_17] :
      ( v1_xboole_0(A_17)
      | ~ v1_xboole_0(k2_relat_1(A_17))
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_26,c_506])).

tff(c_40159,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40130,c_523])).

tff(c_40183,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6,c_40159])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_40197,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40183,c_8])).

tff(c_42,plain,(
    ! [A_35] : m1_subset_1(k6_relat_1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_304,plain,(
    ! [A_90] :
      ( v1_xboole_0(k6_relat_1(A_90))
      | ~ v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_42,c_273])).

tff(c_309,plain,(
    ! [A_91] :
      ( k6_relat_1(A_91) = k1_xboole_0
      | ~ v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_304,c_8])).

tff(c_317,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_309])).

tff(c_28,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_336,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_28])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_473,plain,(
    ! [A_104,B_105] : k1_relset_1(A_104,B_105,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_459])).

tff(c_481,plain,(
    ! [A_104,B_105] : k1_relset_1(A_104,B_105,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_473])).

tff(c_30,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_607,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_610,plain,(
    ! [A_35] : k2_relset_1(A_35,A_35,k6_relat_1(A_35)) = k2_relat_1(k6_relat_1(A_35)) ),
    inference(resolution,[status(thm)],[c_42,c_607])).

tff(c_626,plain,(
    ! [A_35] : k2_relset_1(A_35,A_35,k6_relat_1(A_35)) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_610])).

tff(c_790,plain,(
    ! [A_139,B_140,C_141] :
      ( m1_subset_1(k2_relset_1(A_139,B_140,C_141),k1_zfmisc_1(B_140))
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_822,plain,(
    ! [A_35] :
      ( m1_subset_1(A_35,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(k6_relat_1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_790])).

tff(c_837,plain,(
    ! [A_35] : m1_subset_1(A_35,k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_822])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    ! [C_48,B_47] :
      ( v1_funct_2(C_48,k1_xboole_0,B_47)
      | k1_relset_1(k1_xboole_0,B_47,C_48) != k1_xboole_0
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_928,plain,(
    ! [C_148,B_149] :
      ( v1_funct_2(C_148,k1_xboole_0,B_149)
      | k1_relset_1(k1_xboole_0,B_149,C_148) != k1_xboole_0
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_931,plain,(
    ! [B_149] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_149)
      | k1_relset_1(k1_xboole_0,B_149,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_837,c_928])).

tff(c_946,plain,(
    ! [B_149] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_931])).

tff(c_40409,plain,(
    ! [B_149] : v1_funct_2('#skF_4','#skF_4',B_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40197,c_40197,c_946])).

tff(c_44,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_3'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_554,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_2'(A_116,B_117),k2_relat_1(B_117))
      | ~ r2_hidden(A_116,k1_relat_1(B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_694,plain,(
    ! [B_131,A_132] :
      ( ~ v1_xboole_0(k2_relat_1(B_131))
      | ~ r2_hidden(A_132,k1_relat_1(B_131))
      | ~ v1_relat_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_554,c_2])).

tff(c_716,plain,(
    ! [B_131] :
      ( ~ v1_xboole_0(k2_relat_1(B_131))
      | ~ v1_relat_1(B_131)
      | k1_relat_1(B_131) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_694])).

tff(c_40153,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40130,c_716])).

tff(c_40178,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6,c_40153])).

tff(c_40443,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40197,c_40178])).

tff(c_40132,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40130,c_121])).

tff(c_40198,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40197,c_40132])).

tff(c_40725,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40443,c_40198])).

tff(c_40873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40409,c_40725])).

tff(c_40874,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_40919,plain,(
    ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_40911,c_40874])).

tff(c_41014,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_41008,c_40919])).

tff(c_41025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_41014])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.95/5.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.95/5.69  
% 12.95/5.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.95/5.69  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 12.95/5.69  
% 12.95/5.69  %Foreground sorts:
% 12.95/5.69  
% 12.95/5.69  
% 12.95/5.69  %Background operators:
% 12.95/5.69  
% 12.95/5.69  
% 12.95/5.69  %Foreground operators:
% 12.95/5.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.95/5.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.95/5.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.95/5.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.95/5.69  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.95/5.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.95/5.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.95/5.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.95/5.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.95/5.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.95/5.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.95/5.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.95/5.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.95/5.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.95/5.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.95/5.69  tff('#skF_4', type, '#skF_4': $i).
% 12.95/5.69  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.95/5.69  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.95/5.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.95/5.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.95/5.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.95/5.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.95/5.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.95/5.69  
% 13.22/5.71  tff(f_141, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 13.22/5.71  tff(f_67, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 13.22/5.71  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.22/5.71  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.22/5.71  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.22/5.71  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.22/5.71  tff(f_82, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 13.22/5.71  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 13.22/5.71  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 13.22/5.71  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.22/5.71  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 13.22/5.71  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.22/5.71  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 13.22/5.71  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.22/5.71  tff(f_112, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 13.22/5.71  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 13.22/5.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.22/5.71  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.22/5.71  tff(c_41008, plain, (![A_802]: (r1_tarski(A_802, k2_zfmisc_1(k1_relat_1(A_802), k2_relat_1(A_802))) | ~v1_relat_1(A_802))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.22/5.71  tff(c_40911, plain, (![A_788, B_789]: (m1_subset_1(A_788, k1_zfmisc_1(B_789)) | ~r1_tarski(A_788, B_789))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.22/5.71  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.22/5.71  tff(c_26, plain, (![A_17]: (r1_tarski(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17))) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.22/5.71  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.22/5.71  tff(c_459, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.22/5.71  tff(c_5263, plain, (![A_267, B_268, A_269]: (k1_relset_1(A_267, B_268, A_269)=k1_relat_1(A_269) | ~r1_tarski(A_269, k2_zfmisc_1(A_267, B_268)))), inference(resolution, [status(thm)], [c_20, c_459])).
% 13.22/5.71  tff(c_5311, plain, (![A_17]: (k1_relset_1(k1_relat_1(A_17), k2_relat_1(A_17), A_17)=k1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_26, c_5263])).
% 13.22/5.71  tff(c_1192, plain, (![B_162, C_163, A_164]: (k1_xboole_0=B_162 | v1_funct_2(C_163, A_164, B_162) | k1_relset_1(A_164, B_162, C_163)!=A_164 | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_162))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.22/5.71  tff(c_10777, plain, (![B_393, A_394, A_395]: (k1_xboole_0=B_393 | v1_funct_2(A_394, A_395, B_393) | k1_relset_1(A_395, B_393, A_394)!=A_395 | ~r1_tarski(A_394, k2_zfmisc_1(A_395, B_393)))), inference(resolution, [status(thm)], [c_20, c_1192])).
% 13.22/5.71  tff(c_40013, plain, (![A_768]: (k2_relat_1(A_768)=k1_xboole_0 | v1_funct_2(A_768, k1_relat_1(A_768), k2_relat_1(A_768)) | k1_relset_1(k1_relat_1(A_768), k2_relat_1(A_768), A_768)!=k1_relat_1(A_768) | ~v1_relat_1(A_768))), inference(resolution, [status(thm)], [c_26, c_10777])).
% 13.22/5.71  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.22/5.71  tff(c_62, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.22/5.71  tff(c_68, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62])).
% 13.22/5.71  tff(c_121, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_68])).
% 13.22/5.71  tff(c_40020, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40013, c_121])).
% 13.22/5.71  tff(c_40083, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_40020])).
% 13.22/5.71  tff(c_40122, plain, (k1_relset_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'), '#skF_4')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_40083])).
% 13.22/5.71  tff(c_40125, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5311, c_40122])).
% 13.22/5.71  tff(c_40129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_40125])).
% 13.22/5.71  tff(c_40130, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_40083])).
% 13.22/5.71  tff(c_273, plain, (![C_84, B_85, A_86]: (v1_xboole_0(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(B_85, A_86))) | ~v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.22/5.71  tff(c_506, plain, (![A_110, A_111, B_112]: (v1_xboole_0(A_110) | ~v1_xboole_0(A_111) | ~r1_tarski(A_110, k2_zfmisc_1(B_112, A_111)))), inference(resolution, [status(thm)], [c_20, c_273])).
% 13.22/5.71  tff(c_523, plain, (![A_17]: (v1_xboole_0(A_17) | ~v1_xboole_0(k2_relat_1(A_17)) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_26, c_506])).
% 13.22/5.71  tff(c_40159, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40130, c_523])).
% 13.22/5.71  tff(c_40183, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6, c_40159])).
% 13.22/5.71  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 13.22/5.71  tff(c_40197, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40183, c_8])).
% 13.22/5.71  tff(c_42, plain, (![A_35]: (m1_subset_1(k6_relat_1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.22/5.71  tff(c_304, plain, (![A_90]: (v1_xboole_0(k6_relat_1(A_90)) | ~v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_42, c_273])).
% 13.22/5.71  tff(c_309, plain, (![A_91]: (k6_relat_1(A_91)=k1_xboole_0 | ~v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_304, c_8])).
% 13.22/5.71  tff(c_317, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_309])).
% 13.22/5.71  tff(c_28, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.22/5.71  tff(c_336, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_317, c_28])).
% 13.22/5.71  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.22/5.71  tff(c_473, plain, (![A_104, B_105]: (k1_relset_1(A_104, B_105, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_459])).
% 13.22/5.71  tff(c_481, plain, (![A_104, B_105]: (k1_relset_1(A_104, B_105, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_336, c_473])).
% 13.22/5.71  tff(c_30, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.22/5.71  tff(c_607, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.22/5.71  tff(c_610, plain, (![A_35]: (k2_relset_1(A_35, A_35, k6_relat_1(A_35))=k2_relat_1(k6_relat_1(A_35)))), inference(resolution, [status(thm)], [c_42, c_607])).
% 13.22/5.71  tff(c_626, plain, (![A_35]: (k2_relset_1(A_35, A_35, k6_relat_1(A_35))=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_610])).
% 13.22/5.71  tff(c_790, plain, (![A_139, B_140, C_141]: (m1_subset_1(k2_relset_1(A_139, B_140, C_141), k1_zfmisc_1(B_140)) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.22/5.71  tff(c_822, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1(A_35)) | ~m1_subset_1(k6_relat_1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(superposition, [status(thm), theory('equality')], [c_626, c_790])).
% 13.22/5.71  tff(c_837, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_822])).
% 13.22/5.71  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.22/5.71  tff(c_54, plain, (![C_48, B_47]: (v1_funct_2(C_48, k1_xboole_0, B_47) | k1_relset_1(k1_xboole_0, B_47, C_48)!=k1_xboole_0 | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_47))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.22/5.71  tff(c_928, plain, (![C_148, B_149]: (v1_funct_2(C_148, k1_xboole_0, B_149) | k1_relset_1(k1_xboole_0, B_149, C_148)!=k1_xboole_0 | ~m1_subset_1(C_148, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 13.22/5.71  tff(c_931, plain, (![B_149]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_149) | k1_relset_1(k1_xboole_0, B_149, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_837, c_928])).
% 13.22/5.71  tff(c_946, plain, (![B_149]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_149))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_931])).
% 13.22/5.71  tff(c_40409, plain, (![B_149]: (v1_funct_2('#skF_4', '#skF_4', B_149))), inference(demodulation, [status(thm), theory('equality')], [c_40197, c_40197, c_946])).
% 13.22/5.71  tff(c_44, plain, (![A_36]: (r2_hidden('#skF_3'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_112])).
% 13.22/5.71  tff(c_554, plain, (![A_116, B_117]: (r2_hidden('#skF_2'(A_116, B_117), k2_relat_1(B_117)) | ~r2_hidden(A_116, k1_relat_1(B_117)) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.22/5.71  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.22/5.71  tff(c_694, plain, (![B_131, A_132]: (~v1_xboole_0(k2_relat_1(B_131)) | ~r2_hidden(A_132, k1_relat_1(B_131)) | ~v1_relat_1(B_131))), inference(resolution, [status(thm)], [c_554, c_2])).
% 13.22/5.71  tff(c_716, plain, (![B_131]: (~v1_xboole_0(k2_relat_1(B_131)) | ~v1_relat_1(B_131) | k1_relat_1(B_131)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_694])).
% 13.22/5.71  tff(c_40153, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40130, c_716])).
% 13.22/5.71  tff(c_40178, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6, c_40153])).
% 13.22/5.71  tff(c_40443, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40197, c_40178])).
% 13.22/5.71  tff(c_40132, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40130, c_121])).
% 13.22/5.71  tff(c_40198, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40197, c_40132])).
% 13.22/5.71  tff(c_40725, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40443, c_40198])).
% 13.22/5.71  tff(c_40873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40409, c_40725])).
% 13.22/5.71  tff(c_40874, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))))), inference(splitRight, [status(thm)], [c_68])).
% 13.22/5.71  tff(c_40919, plain, (~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_40911, c_40874])).
% 13.22/5.71  tff(c_41014, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_41008, c_40919])).
% 13.22/5.71  tff(c_41025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_41014])).
% 13.22/5.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.22/5.71  
% 13.22/5.71  Inference rules
% 13.22/5.71  ----------------------
% 13.22/5.71  #Ref     : 0
% 13.22/5.71  #Sup     : 10022
% 13.22/5.71  #Fact    : 0
% 13.22/5.71  #Define  : 0
% 13.22/5.71  #Split   : 5
% 13.22/5.71  #Chain   : 0
% 13.22/5.71  #Close   : 0
% 13.22/5.71  
% 13.22/5.71  Ordering : KBO
% 13.22/5.71  
% 13.22/5.71  Simplification rules
% 13.22/5.71  ----------------------
% 13.22/5.71  #Subsume      : 1580
% 13.22/5.71  #Demod        : 18951
% 13.22/5.71  #Tautology    : 6670
% 13.22/5.71  #SimpNegUnit  : 10
% 13.22/5.71  #BackRed      : 248
% 13.22/5.71  
% 13.22/5.71  #Partial instantiations: 0
% 13.22/5.71  #Strategies tried      : 1
% 13.22/5.71  
% 13.22/5.71  Timing (in seconds)
% 13.22/5.71  ----------------------
% 13.22/5.71  Preprocessing        : 0.35
% 13.22/5.71  Parsing              : 0.18
% 13.22/5.71  CNF conversion       : 0.02
% 13.22/5.71  Main loop            : 4.58
% 13.22/5.71  Inferencing          : 1.02
% 13.22/5.71  Reduction            : 1.67
% 13.22/5.71  Demodulation         : 1.29
% 13.22/5.71  BG Simplification    : 0.13
% 13.22/5.71  Subsumption          : 1.51
% 13.22/5.71  Abstraction          : 0.21
% 13.22/5.71  MUC search           : 0.00
% 13.22/5.71  Cooper               : 0.00
% 13.22/5.71  Total                : 4.98
% 13.22/5.71  Index Insertion      : 0.00
% 13.22/5.71  Index Deletion       : 0.00
% 13.22/5.71  Index Matching       : 0.00
% 13.22/5.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
