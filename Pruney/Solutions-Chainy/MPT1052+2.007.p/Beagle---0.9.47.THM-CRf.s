%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:09 EST 2020

% Result     : Theorem 8.69s
% Output     : CNFRefutation 8.69s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 199 expanded)
%              Number of leaves         :   40 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 409 expanded)
%              Number of equality atoms :   34 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_91,axiom,(
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

tff(f_46,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_20986,plain,(
    ! [B_6041,A_6042] :
      ( r1_tarski(k2_relat_1(B_6041),A_6042)
      | ~ v5_relat_1(B_6041,A_6042)
      | ~ v1_relat_1(B_6041) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_90,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(k1_funct_2(A_45,B_46))
      | ~ v1_xboole_0(B_46)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_94,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_70])).

tff(c_95,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_58,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_77,plain,(
    k1_relat_1('#skF_5') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_127,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_funct_2(C_53,A_54,B_55)
      | ~ r2_hidden(C_53,k1_funct_2(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_141,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_127])).

tff(c_50,plain,(
    ! [C_31,A_29,B_30] :
      ( m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r2_hidden(C_31,k1_funct_2(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_640,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_12057,plain,(
    ! [A_4192,B_4193,C_4194] :
      ( k1_relset_1(A_4192,B_4193,C_4194) = k1_relat_1(C_4194)
      | ~ r2_hidden(C_4194,k1_funct_2(A_4192,B_4193)) ) ),
    inference(resolution,[status(thm)],[c_50,c_640])).

tff(c_12194,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_12057])).

tff(c_13578,plain,(
    ! [B_4549,A_4550,C_4551] :
      ( k1_xboole_0 = B_4549
      | k1_relset_1(A_4550,B_4549,C_4551) = A_4550
      | ~ v1_funct_2(C_4551,A_4550,B_4549)
      | ~ m1_subset_1(C_4551,k1_zfmisc_1(k2_zfmisc_1(A_4550,B_4549))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_19673,plain,(
    ! [B_5854,A_5855,C_5856] :
      ( k1_xboole_0 = B_5854
      | k1_relset_1(A_5855,B_5854,C_5856) = A_5855
      | ~ v1_funct_2(C_5856,A_5855,B_5854)
      | ~ r2_hidden(C_5856,k1_funct_2(A_5855,B_5854)) ) ),
    inference(resolution,[status(thm)],[c_50,c_13578])).

tff(c_19808,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_19673])).

tff(c_19828,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_12194,c_19808])).

tff(c_19829,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_19828])).

tff(c_18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_19910,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19829,c_18])).

tff(c_19912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_19910])).

tff(c_19914,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_19913,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_19916,plain,(
    ! [A_5897,B_5898] :
      ( r2_hidden('#skF_2'(A_5897,B_5898),A_5897)
      | r1_tarski(A_5897,B_5898) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19930,plain,(
    ! [A_5897,B_5898] :
      ( ~ v1_xboole_0(A_5897)
      | r1_tarski(A_5897,B_5898) ) ),
    inference(resolution,[status(thm)],[c_19916,c_2])).

tff(c_19933,plain,(
    ! [A_5902,B_5903] :
      ( r2_xboole_0(A_5902,B_5903)
      | B_5903 = A_5902
      | ~ r1_tarski(A_5902,B_5903) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( ~ r2_xboole_0(B_13,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_19950,plain,(
    ! [B_5904,A_5905] :
      ( ~ r1_tarski(B_5904,A_5905)
      | B_5904 = A_5905
      | ~ r1_tarski(A_5905,B_5904) ) ),
    inference(resolution,[status(thm)],[c_19933,c_20])).

tff(c_19975,plain,(
    ! [B_5909,A_5910] :
      ( B_5909 = A_5910
      | ~ r1_tarski(B_5909,A_5910)
      | ~ v1_xboole_0(A_5910) ) ),
    inference(resolution,[status(thm)],[c_19930,c_19950])).

tff(c_19985,plain,(
    ! [B_5911,A_5912] :
      ( B_5911 = A_5912
      | ~ v1_xboole_0(B_5911)
      | ~ v1_xboole_0(A_5912) ) ),
    inference(resolution,[status(thm)],[c_19930,c_19975])).

tff(c_19998,plain,(
    ! [A_5913] :
      ( A_5913 = '#skF_3'
      | ~ v1_xboole_0(A_5913) ) ),
    inference(resolution,[status(thm)],[c_19913,c_19985])).

tff(c_20011,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_19914,c_19998])).

tff(c_20019,plain,(
    k1_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20011,c_77])).

tff(c_20021,plain,(
    r2_hidden('#skF_5',k1_funct_2('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20011,c_60])).

tff(c_20538,plain,(
    ! [C_5973,A_5974,B_5975] :
      ( m1_subset_1(C_5973,k1_zfmisc_1(k2_zfmisc_1(A_5974,B_5975)))
      | ~ r2_hidden(C_5973,k1_funct_2(A_5974,B_5975)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [C_20,A_18,B_19] :
      ( v4_relat_1(C_20,A_18)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20547,plain,(
    ! [C_5976,A_5977,B_5978] :
      ( v4_relat_1(C_5976,A_5977)
      | ~ r2_hidden(C_5976,k1_funct_2(A_5977,B_5978)) ) ),
    inference(resolution,[status(thm)],[c_20538,c_32])).

tff(c_20579,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_20021,c_20547])).

tff(c_20045,plain,(
    ! [B_5915,A_5916] :
      ( r1_tarski(k1_relat_1(B_5915),A_5916)
      | ~ v4_relat_1(B_5915,A_5916)
      | ~ v1_relat_1(B_5915) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_19955,plain,(
    ! [B_5898,A_5897] :
      ( B_5898 = A_5897
      | ~ r1_tarski(B_5898,A_5897)
      | ~ v1_xboole_0(A_5897) ) ),
    inference(resolution,[status(thm)],[c_19930,c_19950])).

tff(c_20051,plain,(
    ! [B_5915,A_5916] :
      ( k1_relat_1(B_5915) = A_5916
      | ~ v1_xboole_0(A_5916)
      | ~ v4_relat_1(B_5915,A_5916)
      | ~ v1_relat_1(B_5915) ) ),
    inference(resolution,[status(thm)],[c_20045,c_19955])).

tff(c_20584,plain,
    ( k1_relat_1('#skF_5') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20579,c_20051])).

tff(c_20589,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_19914,c_20584])).

tff(c_20591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20019,c_20589])).

tff(c_20592,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_20997,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20986,c_20592])).

tff(c_21003,plain,(
    ~ v5_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20997])).

tff(c_21076,plain,(
    ! [C_6054,A_6055,B_6056] :
      ( m1_subset_1(C_6054,k1_zfmisc_1(k2_zfmisc_1(A_6055,B_6056)))
      | ~ r2_hidden(C_6054,k1_funct_2(A_6055,B_6056)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_30,plain,(
    ! [C_20,B_19,A_18] :
      ( v5_relat_1(C_20,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_21085,plain,(
    ! [C_6057,B_6058,A_6059] :
      ( v5_relat_1(C_6057,B_6058)
      | ~ r2_hidden(C_6057,k1_funct_2(A_6059,B_6058)) ) ),
    inference(resolution,[status(thm)],[c_21076,c_30])).

tff(c_21115,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_21085])).

tff(c_21122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21003,c_21115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:49:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.69/2.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.69/2.88  
% 8.69/2.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.69/2.88  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 8.69/2.88  
% 8.69/2.88  %Foreground sorts:
% 8.69/2.88  
% 8.69/2.88  
% 8.69/2.88  %Background operators:
% 8.69/2.88  
% 8.69/2.88  
% 8.69/2.88  %Foreground operators:
% 8.69/2.88  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 8.69/2.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.69/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.69/2.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.69/2.88  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.69/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.69/2.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.69/2.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.69/2.88  tff('#skF_5', type, '#skF_5': $i).
% 8.69/2.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.69/2.88  tff('#skF_3', type, '#skF_3': $i).
% 8.69/2.88  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.69/2.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.69/2.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.69/2.88  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 8.69/2.88  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 8.69/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.69/2.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.69/2.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.69/2.88  tff('#skF_4', type, '#skF_4': $i).
% 8.69/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.69/2.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.69/2.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.69/2.88  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 8.69/2.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.69/2.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.69/2.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.69/2.88  
% 8.69/2.90  tff(f_119, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 8.69/2.90  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.69/2.90  tff(f_98, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 8.69/2.90  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.69/2.90  tff(f_106, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 8.69/2.90  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.69/2.90  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.69/2.90  tff(f_46, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.69/2.90  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.69/2.90  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 8.69/2.90  tff(f_51, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 8.69/2.90  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.69/2.90  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.69/2.90  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.69/2.90  tff(c_20986, plain, (![B_6041, A_6042]: (r1_tarski(k2_relat_1(B_6041), A_6042) | ~v5_relat_1(B_6041, A_6042) | ~v1_relat_1(B_6041))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.69/2.90  tff(c_90, plain, (![A_45, B_46]: (v1_xboole_0(k1_funct_2(A_45, B_46)) | ~v1_xboole_0(B_46) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.69/2.90  tff(c_60, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.69/2.90  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.69/2.90  tff(c_70, plain, (~v1_xboole_0(k1_funct_2('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_2])).
% 8.69/2.90  tff(c_94, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_90, c_70])).
% 8.69/2.90  tff(c_95, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_94])).
% 8.69/2.90  tff(c_58, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k1_relat_1('#skF_5')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 8.69/2.90  tff(c_77, plain, (k1_relat_1('#skF_5')!='#skF_3'), inference(splitLeft, [status(thm)], [c_58])).
% 8.69/2.90  tff(c_127, plain, (![C_53, A_54, B_55]: (v1_funct_2(C_53, A_54, B_55) | ~r2_hidden(C_53, k1_funct_2(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.69/2.90  tff(c_141, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_127])).
% 8.69/2.90  tff(c_50, plain, (![C_31, A_29, B_30]: (m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r2_hidden(C_31, k1_funct_2(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.69/2.90  tff(c_640, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.69/2.90  tff(c_12057, plain, (![A_4192, B_4193, C_4194]: (k1_relset_1(A_4192, B_4193, C_4194)=k1_relat_1(C_4194) | ~r2_hidden(C_4194, k1_funct_2(A_4192, B_4193)))), inference(resolution, [status(thm)], [c_50, c_640])).
% 8.69/2.90  tff(c_12194, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_12057])).
% 8.69/2.90  tff(c_13578, plain, (![B_4549, A_4550, C_4551]: (k1_xboole_0=B_4549 | k1_relset_1(A_4550, B_4549, C_4551)=A_4550 | ~v1_funct_2(C_4551, A_4550, B_4549) | ~m1_subset_1(C_4551, k1_zfmisc_1(k2_zfmisc_1(A_4550, B_4549))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.69/2.90  tff(c_19673, plain, (![B_5854, A_5855, C_5856]: (k1_xboole_0=B_5854 | k1_relset_1(A_5855, B_5854, C_5856)=A_5855 | ~v1_funct_2(C_5856, A_5855, B_5854) | ~r2_hidden(C_5856, k1_funct_2(A_5855, B_5854)))), inference(resolution, [status(thm)], [c_50, c_13578])).
% 8.69/2.90  tff(c_19808, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_19673])).
% 8.69/2.90  tff(c_19828, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_12194, c_19808])).
% 8.69/2.90  tff(c_19829, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_77, c_19828])).
% 8.69/2.90  tff(c_18, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.69/2.90  tff(c_19910, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19829, c_18])).
% 8.69/2.90  tff(c_19912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_19910])).
% 8.69/2.90  tff(c_19914, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_94])).
% 8.69/2.90  tff(c_19913, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_94])).
% 8.69/2.90  tff(c_19916, plain, (![A_5897, B_5898]: (r2_hidden('#skF_2'(A_5897, B_5898), A_5897) | r1_tarski(A_5897, B_5898))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.69/2.90  tff(c_19930, plain, (![A_5897, B_5898]: (~v1_xboole_0(A_5897) | r1_tarski(A_5897, B_5898))), inference(resolution, [status(thm)], [c_19916, c_2])).
% 8.69/2.90  tff(c_19933, plain, (![A_5902, B_5903]: (r2_xboole_0(A_5902, B_5903) | B_5903=A_5902 | ~r1_tarski(A_5902, B_5903))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.69/2.90  tff(c_20, plain, (![B_13, A_12]: (~r2_xboole_0(B_13, A_12) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.69/2.90  tff(c_19950, plain, (![B_5904, A_5905]: (~r1_tarski(B_5904, A_5905) | B_5904=A_5905 | ~r1_tarski(A_5905, B_5904))), inference(resolution, [status(thm)], [c_19933, c_20])).
% 8.69/2.90  tff(c_19975, plain, (![B_5909, A_5910]: (B_5909=A_5910 | ~r1_tarski(B_5909, A_5910) | ~v1_xboole_0(A_5910))), inference(resolution, [status(thm)], [c_19930, c_19950])).
% 8.69/2.90  tff(c_19985, plain, (![B_5911, A_5912]: (B_5911=A_5912 | ~v1_xboole_0(B_5911) | ~v1_xboole_0(A_5912))), inference(resolution, [status(thm)], [c_19930, c_19975])).
% 8.69/2.90  tff(c_19998, plain, (![A_5913]: (A_5913='#skF_3' | ~v1_xboole_0(A_5913))), inference(resolution, [status(thm)], [c_19913, c_19985])).
% 8.69/2.90  tff(c_20011, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_19914, c_19998])).
% 8.69/2.90  tff(c_20019, plain, (k1_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20011, c_77])).
% 8.69/2.90  tff(c_20021, plain, (r2_hidden('#skF_5', k1_funct_2('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20011, c_60])).
% 8.69/2.90  tff(c_20538, plain, (![C_5973, A_5974, B_5975]: (m1_subset_1(C_5973, k1_zfmisc_1(k2_zfmisc_1(A_5974, B_5975))) | ~r2_hidden(C_5973, k1_funct_2(A_5974, B_5975)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.69/2.90  tff(c_32, plain, (![C_20, A_18, B_19]: (v4_relat_1(C_20, A_18) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.69/2.90  tff(c_20547, plain, (![C_5976, A_5977, B_5978]: (v4_relat_1(C_5976, A_5977) | ~r2_hidden(C_5976, k1_funct_2(A_5977, B_5978)))), inference(resolution, [status(thm)], [c_20538, c_32])).
% 8.69/2.90  tff(c_20579, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_20021, c_20547])).
% 8.69/2.90  tff(c_20045, plain, (![B_5915, A_5916]: (r1_tarski(k1_relat_1(B_5915), A_5916) | ~v4_relat_1(B_5915, A_5916) | ~v1_relat_1(B_5915))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.69/2.90  tff(c_19955, plain, (![B_5898, A_5897]: (B_5898=A_5897 | ~r1_tarski(B_5898, A_5897) | ~v1_xboole_0(A_5897))), inference(resolution, [status(thm)], [c_19930, c_19950])).
% 8.69/2.90  tff(c_20051, plain, (![B_5915, A_5916]: (k1_relat_1(B_5915)=A_5916 | ~v1_xboole_0(A_5916) | ~v4_relat_1(B_5915, A_5916) | ~v1_relat_1(B_5915))), inference(resolution, [status(thm)], [c_20045, c_19955])).
% 8.69/2.90  tff(c_20584, plain, (k1_relat_1('#skF_5')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20579, c_20051])).
% 8.69/2.90  tff(c_20589, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_19914, c_20584])).
% 8.69/2.90  tff(c_20591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20019, c_20589])).
% 8.69/2.90  tff(c_20592, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_58])).
% 8.69/2.90  tff(c_20997, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_20986, c_20592])).
% 8.69/2.90  tff(c_21003, plain, (~v5_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20997])).
% 8.69/2.90  tff(c_21076, plain, (![C_6054, A_6055, B_6056]: (m1_subset_1(C_6054, k1_zfmisc_1(k2_zfmisc_1(A_6055, B_6056))) | ~r2_hidden(C_6054, k1_funct_2(A_6055, B_6056)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.69/2.90  tff(c_30, plain, (![C_20, B_19, A_18]: (v5_relat_1(C_20, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.69/2.90  tff(c_21085, plain, (![C_6057, B_6058, A_6059]: (v5_relat_1(C_6057, B_6058) | ~r2_hidden(C_6057, k1_funct_2(A_6059, B_6058)))), inference(resolution, [status(thm)], [c_21076, c_30])).
% 8.69/2.90  tff(c_21115, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_21085])).
% 8.69/2.90  tff(c_21122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21003, c_21115])).
% 8.69/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.69/2.90  
% 8.69/2.90  Inference rules
% 8.69/2.90  ----------------------
% 8.69/2.90  #Ref     : 0
% 8.69/2.90  #Sup     : 2601
% 8.69/2.90  #Fact    : 4
% 8.69/2.90  #Define  : 0
% 8.69/2.90  #Split   : 11
% 8.69/2.90  #Chain   : 0
% 8.89/2.90  #Close   : 0
% 8.89/2.90  
% 8.89/2.90  Ordering : KBO
% 8.89/2.90  
% 8.89/2.90  Simplification rules
% 8.89/2.90  ----------------------
% 8.89/2.90  #Subsume      : 917
% 8.89/2.90  #Demod        : 629
% 8.89/2.90  #Tautology    : 467
% 8.89/2.90  #SimpNegUnit  : 37
% 8.89/2.90  #BackRed      : 151
% 8.89/2.90  
% 8.89/2.90  #Partial instantiations: 4116
% 8.89/2.90  #Strategies tried      : 1
% 8.89/2.90  
% 8.89/2.90  Timing (in seconds)
% 8.89/2.90  ----------------------
% 8.89/2.91  Preprocessing        : 0.34
% 8.89/2.91  Parsing              : 0.18
% 8.89/2.91  CNF conversion       : 0.02
% 8.89/2.91  Main loop            : 1.75
% 8.89/2.91  Inferencing          : 0.67
% 8.89/2.91  Reduction            : 0.42
% 8.89/2.91  Demodulation         : 0.28
% 8.89/2.91  BG Simplification    : 0.06
% 8.89/2.91  Subsumption          : 0.47
% 8.89/2.91  Abstraction          : 0.07
% 8.89/2.91  MUC search           : 0.00
% 8.89/2.91  Cooper               : 0.00
% 8.89/2.91  Total                : 2.12
% 8.89/2.91  Index Insertion      : 0.00
% 8.89/2.91  Index Deletion       : 0.00
% 8.89/2.91  Index Matching       : 0.00
% 8.89/2.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
