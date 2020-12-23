%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:44 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 494 expanded)
%              Number of leaves         :   36 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  255 (1469 expanded)
%              Number of equality atoms :   61 ( 322 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_70,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_24,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_115,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_128,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_121])).

tff(c_173,plain,(
    ! [A_76] :
      ( '#skF_2'(A_76) != '#skF_1'(A_76)
      | v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_176,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_70])).

tff(c_179,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_46,c_176])).

tff(c_370,plain,(
    ! [A_96] :
      ( k1_funct_1(A_96,'#skF_2'(A_96)) = k1_funct_1(A_96,'#skF_1'(A_96))
      | v2_funct_1(A_96)
      | ~ v1_funct_1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_66,plain,(
    ! [D_43,C_42] :
      ( v2_funct_1('#skF_4')
      | D_43 = C_42
      | k1_funct_1('#skF_4',D_43) != k1_funct_1('#skF_4',C_42)
      | ~ r2_hidden(D_43,'#skF_3')
      | ~ r2_hidden(C_42,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_130,plain,(
    ! [D_43,C_42] :
      ( D_43 = C_42
      | k1_funct_1('#skF_4',D_43) != k1_funct_1('#skF_4',C_42)
      | ~ r2_hidden(D_43,'#skF_3')
      | ~ r2_hidden(C_42,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_66])).

tff(c_379,plain,(
    ! [D_43] :
      ( D_43 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_43) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_43,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_130])).

tff(c_388,plain,(
    ! [D_43] :
      ( D_43 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_43) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_43,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_46,c_379])).

tff(c_389,plain,(
    ! [D_43] :
      ( D_43 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_43) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_43,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_388])).

tff(c_434,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_204,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_217,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_204])).

tff(c_256,plain,(
    ! [A_91,B_92,C_93] :
      ( m1_subset_1(k1_relset_1(A_91,B_92,C_93),k1_zfmisc_1(A_91))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_277,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_256])).

tff(c_285,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_277])).

tff(c_191,plain,(
    ! [A_78] :
      ( r2_hidden('#skF_2'(A_78),k1_relat_1(A_78))
      | v2_funct_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_10,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_833,plain,(
    ! [A_147,A_148] :
      ( r2_hidden('#skF_2'(A_147),A_148)
      | ~ m1_subset_1(k1_relat_1(A_147),k1_zfmisc_1(A_148))
      | v2_funct_1(A_147)
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_191,c_10])).

tff(c_839,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_285,c_833])).

tff(c_851,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_46,c_839])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_434,c_851])).

tff(c_855,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_376,plain,(
    ! [C_42] :
      ( C_42 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_42) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_42,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_130])).

tff(c_385,plain,(
    ! [C_42] :
      ( C_42 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_42) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_42,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_46,c_376])).

tff(c_386,plain,(
    ! [C_42] :
      ( C_42 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_42) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_42,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_385])).

tff(c_946,plain,(
    ! [C_42] :
      ( C_42 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_42) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_42,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_855,c_386])).

tff(c_949,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_946])).

tff(c_950,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_949])).

tff(c_180,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_1'(A_77),k1_relat_1(A_77))
      | v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1507,plain,(
    ! [A_213,A_214] :
      ( r2_hidden('#skF_1'(A_213),A_214)
      | ~ m1_subset_1(k1_relat_1(A_213),k1_zfmisc_1(A_214))
      | v2_funct_1(A_213)
      | ~ v1_funct_1(A_213)
      | ~ v1_relat_1(A_213) ) ),
    inference(resolution,[status(thm)],[c_180,c_10])).

tff(c_1513,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_285,c_1507])).

tff(c_1525,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_46,c_1513])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_950,c_1525])).

tff(c_1529,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_50,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1556,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_50])).

tff(c_54,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1535,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_54])).

tff(c_2074,plain,(
    ! [D_286,C_287,B_288,A_289] :
      ( k1_funct_1(k2_funct_1(D_286),k1_funct_1(D_286,C_287)) = C_287
      | k1_xboole_0 = B_288
      | ~ r2_hidden(C_287,A_289)
      | ~ v2_funct_1(D_286)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(A_289,B_288)))
      | ~ v1_funct_2(D_286,A_289,B_288)
      | ~ v1_funct_1(D_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2093,plain,(
    ! [D_290,B_291] :
      ( k1_funct_1(k2_funct_1(D_290),k1_funct_1(D_290,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_291
      | ~ v2_funct_1(D_290)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_291)))
      | ~ v1_funct_2(D_290,'#skF_3',B_291)
      | ~ v1_funct_1(D_290) ) ),
    inference(resolution,[status(thm)],[c_1535,c_2074])).

tff(c_2101,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2093])).

tff(c_2109,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1529,c_1556,c_2101])).

tff(c_2111,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2109])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1533,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_52])).

tff(c_1655,plain,(
    ! [C_241,A_242,B_243] :
      ( r2_hidden(C_241,A_242)
      | ~ r2_hidden(C_241,B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(A_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1669,plain,(
    ! [A_245] :
      ( r2_hidden('#skF_6',A_245)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_245)) ) ),
    inference(resolution,[status(thm)],[c_1533,c_1655])).

tff(c_1675,plain,(
    ! [B_246] :
      ( r2_hidden('#skF_6',B_246)
      | ~ r1_tarski('#skF_3',B_246) ) ),
    inference(resolution,[status(thm)],[c_18,c_1669])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1607,plain,(
    ! [A_229,C_230,B_231] :
      ( m1_subset_1(A_229,C_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(C_230))
      | ~ r2_hidden(A_229,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1616,plain,(
    ! [A_229,A_8] :
      ( m1_subset_1(A_229,A_8)
      | ~ r2_hidden(A_229,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_1607])).

tff(c_1688,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_6',A_8)
      | ~ r1_tarski('#skF_3',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1675,c_1616])).

tff(c_1691,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1688])).

tff(c_2117,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2111,c_1691])).

tff(c_2125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2117])).

tff(c_2127,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2109])).

tff(c_1528,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2126,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2109])).

tff(c_2260,plain,(
    ! [D_303,B_304] :
      ( k1_funct_1(k2_funct_1(D_303),k1_funct_1(D_303,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_304
      | ~ v2_funct_1(D_303)
      | ~ m1_subset_1(D_303,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_304)))
      | ~ v1_funct_2(D_303,'#skF_3',B_304)
      | ~ v1_funct_1(D_303) ) ),
    inference(resolution,[status(thm)],[c_1533,c_2074])).

tff(c_2268,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_2260])).

tff(c_2276,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1529,c_2126,c_2268])).

tff(c_2278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2127,c_1528,c_2276])).

tff(c_2283,plain,(
    ! [A_305] : m1_subset_1('#skF_6',A_305) ),
    inference(splitRight,[status(thm)],[c_1688])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2297,plain,(
    ! [B_12] : r1_tarski('#skF_6',B_12) ),
    inference(resolution,[status(thm)],[c_2283,c_16])).

tff(c_2280,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1688])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1566,plain,(
    ! [B_224,A_225] :
      ( B_224 = A_225
      | ~ r1_tarski(B_224,A_225)
      | ~ r1_tarski(A_225,B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1578,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1566])).

tff(c_2313,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2280,c_1578])).

tff(c_2439,plain,(
    ! [A_314] :
      ( A_314 = '#skF_3'
      | ~ r1_tarski(A_314,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_2313,c_1578])).

tff(c_2457,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2297,c_2439])).

tff(c_2478,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2457,c_1528])).

tff(c_2322,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2313,c_8])).

tff(c_1641,plain,(
    ! [A_237,B_238,A_239] :
      ( m1_subset_1(A_237,B_238)
      | ~ r2_hidden(A_237,A_239)
      | ~ r1_tarski(A_239,B_238) ) ),
    inference(resolution,[status(thm)],[c_18,c_1607])).

tff(c_1646,plain,(
    ! [B_238] :
      ( m1_subset_1('#skF_5',B_238)
      | ~ r1_tarski('#skF_3',B_238) ) ),
    inference(resolution,[status(thm)],[c_1535,c_1641])).

tff(c_2355,plain,(
    ! [B_309] : m1_subset_1('#skF_5',B_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2322,c_1646])).

tff(c_2369,plain,(
    ! [B_12] : r1_tarski('#skF_5',B_12) ),
    inference(resolution,[status(thm)],[c_2355,c_16])).

tff(c_2456,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2369,c_2439])).

tff(c_2485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2478,c_2456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.79  
% 4.57/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.57/1.79  
% 4.57/1.79  %Foreground sorts:
% 4.57/1.79  
% 4.57/1.79  
% 4.57/1.79  %Background operators:
% 4.57/1.79  
% 4.57/1.79  
% 4.57/1.79  %Foreground operators:
% 4.57/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.57/1.79  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.57/1.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.57/1.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.57/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.57/1.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.57/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.57/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.57/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.57/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.57/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.57/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.57/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.57/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.57/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.57/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.57/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.57/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.57/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.57/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.57/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.57/1.79  
% 4.66/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.66/1.81  tff(f_120, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 4.66/1.81  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.66/1.81  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.66/1.81  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 4.66/1.81  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.66/1.81  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.66/1.81  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.66/1.81  tff(f_102, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 4.66/1.81  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.66/1.81  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.66/1.81  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.66/1.81  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.66/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.81  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_48, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_70, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 4.66/1.81  tff(c_24, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.66/1.81  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_115, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.66/1.81  tff(c_121, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_115])).
% 4.66/1.81  tff(c_128, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_121])).
% 4.66/1.81  tff(c_173, plain, (![A_76]: ('#skF_2'(A_76)!='#skF_1'(A_76) | v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.66/1.81  tff(c_176, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_173, c_70])).
% 4.66/1.81  tff(c_179, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_46, c_176])).
% 4.66/1.81  tff(c_370, plain, (![A_96]: (k1_funct_1(A_96, '#skF_2'(A_96))=k1_funct_1(A_96, '#skF_1'(A_96)) | v2_funct_1(A_96) | ~v1_funct_1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.66/1.81  tff(c_66, plain, (![D_43, C_42]: (v2_funct_1('#skF_4') | D_43=C_42 | k1_funct_1('#skF_4', D_43)!=k1_funct_1('#skF_4', C_42) | ~r2_hidden(D_43, '#skF_3') | ~r2_hidden(C_42, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_130, plain, (![D_43, C_42]: (D_43=C_42 | k1_funct_1('#skF_4', D_43)!=k1_funct_1('#skF_4', C_42) | ~r2_hidden(D_43, '#skF_3') | ~r2_hidden(C_42, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_66])).
% 4.66/1.81  tff(c_379, plain, (![D_43]: (D_43='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_43)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_43, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_370, c_130])).
% 4.66/1.81  tff(c_388, plain, (![D_43]: (D_43='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_43)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_43, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_46, c_379])).
% 4.66/1.81  tff(c_389, plain, (![D_43]: (D_43='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_43)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_43, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_388])).
% 4.66/1.81  tff(c_434, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_389])).
% 4.66/1.81  tff(c_204, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.66/1.81  tff(c_217, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_204])).
% 4.66/1.81  tff(c_256, plain, (![A_91, B_92, C_93]: (m1_subset_1(k1_relset_1(A_91, B_92, C_93), k1_zfmisc_1(A_91)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.66/1.81  tff(c_277, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_217, c_256])).
% 4.66/1.81  tff(c_285, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_277])).
% 4.66/1.81  tff(c_191, plain, (![A_78]: (r2_hidden('#skF_2'(A_78), k1_relat_1(A_78)) | v2_funct_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.66/1.81  tff(c_10, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.66/1.81  tff(c_833, plain, (![A_147, A_148]: (r2_hidden('#skF_2'(A_147), A_148) | ~m1_subset_1(k1_relat_1(A_147), k1_zfmisc_1(A_148)) | v2_funct_1(A_147) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_191, c_10])).
% 4.66/1.81  tff(c_839, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_285, c_833])).
% 4.66/1.81  tff(c_851, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_46, c_839])).
% 4.66/1.81  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_434, c_851])).
% 4.66/1.81  tff(c_855, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_389])).
% 4.66/1.81  tff(c_376, plain, (![C_42]: (C_42='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_42)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_42, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_370, c_130])).
% 4.66/1.81  tff(c_385, plain, (![C_42]: (C_42='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_42)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_42, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_46, c_376])).
% 4.66/1.81  tff(c_386, plain, (![C_42]: (C_42='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_42)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_42, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_70, c_385])).
% 4.66/1.81  tff(c_946, plain, (![C_42]: (C_42='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_42)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_42, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_855, c_386])).
% 4.66/1.81  tff(c_949, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_946])).
% 4.66/1.81  tff(c_950, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_179, c_949])).
% 4.66/1.81  tff(c_180, plain, (![A_77]: (r2_hidden('#skF_1'(A_77), k1_relat_1(A_77)) | v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.66/1.81  tff(c_1507, plain, (![A_213, A_214]: (r2_hidden('#skF_1'(A_213), A_214) | ~m1_subset_1(k1_relat_1(A_213), k1_zfmisc_1(A_214)) | v2_funct_1(A_213) | ~v1_funct_1(A_213) | ~v1_relat_1(A_213))), inference(resolution, [status(thm)], [c_180, c_10])).
% 4.66/1.81  tff(c_1513, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_285, c_1507])).
% 4.66/1.81  tff(c_1525, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_46, c_1513])).
% 4.66/1.81  tff(c_1527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_950, c_1525])).
% 4.66/1.81  tff(c_1529, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 4.66/1.81  tff(c_50, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_1556, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_50])).
% 4.66/1.81  tff(c_54, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_1535, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_54])).
% 4.66/1.81  tff(c_2074, plain, (![D_286, C_287, B_288, A_289]: (k1_funct_1(k2_funct_1(D_286), k1_funct_1(D_286, C_287))=C_287 | k1_xboole_0=B_288 | ~r2_hidden(C_287, A_289) | ~v2_funct_1(D_286) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(A_289, B_288))) | ~v1_funct_2(D_286, A_289, B_288) | ~v1_funct_1(D_286))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.66/1.81  tff(c_2093, plain, (![D_290, B_291]: (k1_funct_1(k2_funct_1(D_290), k1_funct_1(D_290, '#skF_5'))='#skF_5' | k1_xboole_0=B_291 | ~v2_funct_1(D_290) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_291))) | ~v1_funct_2(D_290, '#skF_3', B_291) | ~v1_funct_1(D_290))), inference(resolution, [status(thm)], [c_1535, c_2074])).
% 4.66/1.81  tff(c_2101, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2093])).
% 4.66/1.81  tff(c_2109, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1529, c_1556, c_2101])).
% 4.66/1.81  tff(c_2111, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2109])).
% 4.66/1.81  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.66/1.81  tff(c_52, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.66/1.81  tff(c_1533, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1529, c_52])).
% 4.66/1.81  tff(c_1655, plain, (![C_241, A_242, B_243]: (r2_hidden(C_241, A_242) | ~r2_hidden(C_241, B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(A_242)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.66/1.81  tff(c_1669, plain, (![A_245]: (r2_hidden('#skF_6', A_245) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_245)))), inference(resolution, [status(thm)], [c_1533, c_1655])).
% 4.66/1.81  tff(c_1675, plain, (![B_246]: (r2_hidden('#skF_6', B_246) | ~r1_tarski('#skF_3', B_246))), inference(resolution, [status(thm)], [c_18, c_1669])).
% 4.66/1.81  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.66/1.81  tff(c_1607, plain, (![A_229, C_230, B_231]: (m1_subset_1(A_229, C_230) | ~m1_subset_1(B_231, k1_zfmisc_1(C_230)) | ~r2_hidden(A_229, B_231))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.66/1.81  tff(c_1616, plain, (![A_229, A_8]: (m1_subset_1(A_229, A_8) | ~r2_hidden(A_229, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1607])).
% 4.66/1.81  tff(c_1688, plain, (![A_8]: (m1_subset_1('#skF_6', A_8) | ~r1_tarski('#skF_3', k1_xboole_0))), inference(resolution, [status(thm)], [c_1675, c_1616])).
% 4.66/1.81  tff(c_1691, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1688])).
% 4.66/1.81  tff(c_2117, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2111, c_1691])).
% 4.66/1.81  tff(c_2125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2117])).
% 4.66/1.81  tff(c_2127, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2109])).
% 4.66/1.81  tff(c_1528, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_48])).
% 4.66/1.81  tff(c_2126, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_2109])).
% 4.66/1.81  tff(c_2260, plain, (![D_303, B_304]: (k1_funct_1(k2_funct_1(D_303), k1_funct_1(D_303, '#skF_6'))='#skF_6' | k1_xboole_0=B_304 | ~v2_funct_1(D_303) | ~m1_subset_1(D_303, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_304))) | ~v1_funct_2(D_303, '#skF_3', B_304) | ~v1_funct_1(D_303))), inference(resolution, [status(thm)], [c_1533, c_2074])).
% 4.66/1.81  tff(c_2268, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_2260])).
% 4.66/1.81  tff(c_2276, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1529, c_2126, c_2268])).
% 4.66/1.81  tff(c_2278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2127, c_1528, c_2276])).
% 4.66/1.81  tff(c_2283, plain, (![A_305]: (m1_subset_1('#skF_6', A_305))), inference(splitRight, [status(thm)], [c_1688])).
% 4.66/1.81  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.66/1.81  tff(c_2297, plain, (![B_12]: (r1_tarski('#skF_6', B_12))), inference(resolution, [status(thm)], [c_2283, c_16])).
% 4.66/1.81  tff(c_2280, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1688])).
% 4.66/1.81  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.66/1.81  tff(c_1566, plain, (![B_224, A_225]: (B_224=A_225 | ~r1_tarski(B_224, A_225) | ~r1_tarski(A_225, B_224))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.81  tff(c_1578, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1566])).
% 4.66/1.81  tff(c_2313, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_2280, c_1578])).
% 4.66/1.81  tff(c_2439, plain, (![A_314]: (A_314='#skF_3' | ~r1_tarski(A_314, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_2313, c_1578])).
% 4.66/1.81  tff(c_2457, plain, ('#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_2297, c_2439])).
% 4.66/1.81  tff(c_2478, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2457, c_1528])).
% 4.66/1.81  tff(c_2322, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2313, c_8])).
% 4.66/1.81  tff(c_1641, plain, (![A_237, B_238, A_239]: (m1_subset_1(A_237, B_238) | ~r2_hidden(A_237, A_239) | ~r1_tarski(A_239, B_238))), inference(resolution, [status(thm)], [c_18, c_1607])).
% 4.66/1.81  tff(c_1646, plain, (![B_238]: (m1_subset_1('#skF_5', B_238) | ~r1_tarski('#skF_3', B_238))), inference(resolution, [status(thm)], [c_1535, c_1641])).
% 4.66/1.81  tff(c_2355, plain, (![B_309]: (m1_subset_1('#skF_5', B_309))), inference(demodulation, [status(thm), theory('equality')], [c_2322, c_1646])).
% 4.66/1.81  tff(c_2369, plain, (![B_12]: (r1_tarski('#skF_5', B_12))), inference(resolution, [status(thm)], [c_2355, c_16])).
% 4.66/1.81  tff(c_2456, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_2369, c_2439])).
% 4.66/1.81  tff(c_2485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2478, c_2456])).
% 4.66/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.81  
% 4.66/1.81  Inference rules
% 4.66/1.81  ----------------------
% 4.66/1.81  #Ref     : 4
% 4.66/1.81  #Sup     : 510
% 4.66/1.81  #Fact    : 0
% 4.66/1.81  #Define  : 0
% 4.66/1.81  #Split   : 24
% 4.66/1.81  #Chain   : 0
% 4.66/1.81  #Close   : 0
% 4.66/1.81  
% 4.66/1.81  Ordering : KBO
% 4.66/1.81  
% 4.66/1.81  Simplification rules
% 4.66/1.81  ----------------------
% 4.66/1.81  #Subsume      : 101
% 4.66/1.81  #Demod        : 316
% 4.66/1.81  #Tautology    : 177
% 4.66/1.81  #SimpNegUnit  : 31
% 4.66/1.81  #BackRed      : 42
% 4.66/1.81  
% 4.66/1.81  #Partial instantiations: 0
% 4.66/1.81  #Strategies tried      : 1
% 4.66/1.81  
% 4.66/1.81  Timing (in seconds)
% 4.66/1.81  ----------------------
% 4.70/1.82  Preprocessing        : 0.35
% 4.70/1.82  Parsing              : 0.18
% 4.70/1.82  CNF conversion       : 0.03
% 4.70/1.82  Main loop            : 0.67
% 4.70/1.82  Inferencing          : 0.23
% 4.70/1.82  Reduction            : 0.22
% 4.70/1.82  Demodulation         : 0.15
% 4.70/1.82  BG Simplification    : 0.03
% 4.70/1.82  Subsumption          : 0.13
% 4.70/1.82  Abstraction          : 0.03
% 4.70/1.82  MUC search           : 0.00
% 4.70/1.82  Cooper               : 0.00
% 4.70/1.82  Total                : 1.08
% 4.70/1.82  Index Insertion      : 0.00
% 4.70/1.82  Index Deletion       : 0.00
% 4.70/1.82  Index Matching       : 0.00
% 4.70/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
