%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:31 EST 2020

% Result     : Theorem 10.14s
% Output     : CNFRefutation 10.51s
% Verified   : 
% Statistics : Number of formulae       :  341 (32960 expanded)
%              Number of leaves         :   43 (10609 expanded)
%              Depth                    :   20
%              Number of atoms          :  619 (77703 expanded)
%              Number of equality atoms :  170 (13395 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_161,negated_conjecture,(
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

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_134,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_144,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_116,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_494,plain,(
    ! [C_111,B_112,A_113] :
      ( v1_xboole_0(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(B_112,A_113)))
      | ~ v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_512,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_494])).

tff(c_527,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_154,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_167,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_154])).

tff(c_82,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_30,plain,(
    ! [A_16] :
      ( v1_funct_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_168,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_171,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_82,c_171])).

tff(c_176,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_204,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_76,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_80,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_996,plain,(
    ! [A_147,B_148,C_149] :
      ( k1_relset_1(A_147,B_148,C_149) = k1_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1027,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_996])).

tff(c_1573,plain,(
    ! [B_219,A_220,C_221] :
      ( k1_xboole_0 = B_219
      | k1_relset_1(A_220,B_219,C_221) = A_220
      | ~ v1_funct_2(C_221,A_220,B_219)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1598,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_1573])).

tff(c_1612,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1027,c_1598])).

tff(c_1614,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1612])).

tff(c_34,plain,(
    ! [A_17] :
      ( k2_relat_1(k2_funct_1(A_17)) = k1_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_32,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_177,plain,(
    v1_funct_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_74,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1044,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1066,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_1044])).

tff(c_1076,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1066])).

tff(c_515,plain,(
    ! [A_114] :
      ( k1_relat_1(k2_funct_1(A_114)) = k2_relat_1(A_114)
      | ~ v2_funct_1(A_114)
      | ~ v1_funct_1(A_114)
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ! [A_45] :
      ( v1_funct_2(A_45,k1_relat_1(A_45),k2_relat_1(A_45))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4192,plain,(
    ! [A_392] :
      ( v1_funct_2(k2_funct_1(A_392),k2_relat_1(A_392),k2_relat_1(k2_funct_1(A_392)))
      | ~ v1_funct_1(k2_funct_1(A_392))
      | ~ v1_relat_1(k2_funct_1(A_392))
      | ~ v2_funct_1(A_392)
      | ~ v1_funct_1(A_392)
      | ~ v1_relat_1(A_392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_68])).

tff(c_4210,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_4192])).

tff(c_4227,plain,
    ( v1_funct_2(k2_funct_1('#skF_5'),'#skF_4',k2_relat_1(k2_funct_1('#skF_5')))
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_82,c_76,c_177,c_4210])).

tff(c_4228,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4227])).

tff(c_4231,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_4228])).

tff(c_4235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_82,c_4231])).

tff(c_4237,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4227])).

tff(c_36,plain,(
    ! [A_17] :
      ( k1_relat_1(k2_funct_1(A_17)) = k2_relat_1(A_17)
      | ~ v2_funct_1(A_17)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_839,plain,(
    ! [A_137] :
      ( m1_subset_1(A_137,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_137),k2_relat_1(A_137))))
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4910,plain,(
    ! [A_431] :
      ( m1_subset_1(k2_funct_1(A_431),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_431),k2_relat_1(k2_funct_1(A_431)))))
      | ~ v1_funct_1(k2_funct_1(A_431))
      | ~ v1_relat_1(k2_funct_1(A_431))
      | ~ v2_funct_1(A_431)
      | ~ v1_funct_1(A_431)
      | ~ v1_relat_1(A_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_839])).

tff(c_4955,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5')))))
    | ~ v1_funct_1(k2_funct_1('#skF_5'))
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_4910])).

tff(c_4981,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_82,c_76,c_4237,c_177,c_4955])).

tff(c_5014,plain,
    ( m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_5'))))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4981])).

tff(c_5035,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_82,c_76,c_1614,c_5014])).

tff(c_5037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_5035])).

tff(c_5038,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1612])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5083,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5038,c_12])).

tff(c_5085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_527,c_5083])).

tff(c_5087,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_184,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_2'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [A_66,B_67] :
      ( ~ v1_xboole_0(A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_189,plain,(
    ! [A_68,B_69] :
      ( ~ v1_xboole_0(A_68)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_184,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_189,c_14])).

tff(c_268,plain,(
    ! [B_81,A_82] :
      ( B_81 = A_82
      | ~ v1_xboole_0(B_81)
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_188,c_253])).

tff(c_271,plain,(
    ! [A_82] :
      ( k1_xboole_0 = A_82
      | ~ v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_12,c_268])).

tff(c_5120,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5087,c_271])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5135,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5120,c_5120,c_22])).

tff(c_122,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_78,c_122])).

tff(c_264,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_126,c_253])).

tff(c_267,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_5217,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5135,c_267])).

tff(c_5220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5087,c_5217])).

tff(c_5221,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_5222,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_5247,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_5222])).

tff(c_5272,plain,(
    ! [B_441,A_442] :
      ( B_441 = A_442
      | ~ v1_xboole_0(B_441)
      | ~ v1_xboole_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_188,c_253])).

tff(c_5279,plain,(
    ! [A_443] :
      ( k1_xboole_0 = A_443
      | ~ v1_xboole_0(A_443) ) ),
    inference(resolution,[status(thm)],[c_12,c_5272])).

tff(c_5286,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5247,c_5279])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5235,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5221,c_20])).

tff(c_5374,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_5286,c_5235])).

tff(c_5375,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5374])).

tff(c_5295,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_22])).

tff(c_5377,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_5375,c_5295])).

tff(c_5387,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_204])).

tff(c_5516,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5377,c_5387])).

tff(c_5389,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_167])).

tff(c_5393,plain,(
    v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_82])).

tff(c_5392,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_76])).

tff(c_5224,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_78])).

tff(c_5382,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_5375,c_5224])).

tff(c_5383,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_5247])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6248,plain,(
    ! [A_527,B_528,C_529] :
      ( k1_relset_1(A_527,B_528,C_529) = k1_relat_1(C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_527,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6456,plain,(
    ! [A_567,B_568,A_569] :
      ( k1_relset_1(A_567,B_568,A_569) = k1_relat_1(A_569)
      | ~ r1_tarski(A_569,k2_zfmisc_1(A_567,B_568)) ) ),
    inference(resolution,[status(thm)],[c_28,c_6248])).

tff(c_6485,plain,(
    ! [A_570,B_571,A_572] :
      ( k1_relset_1(A_570,B_571,A_572) = k1_relat_1(A_572)
      | ~ v1_xboole_0(A_572) ) ),
    inference(resolution,[status(thm)],[c_188,c_6456])).

tff(c_6494,plain,(
    ! [A_570,B_571] : k1_relset_1(A_570,B_571,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5383,c_6485])).

tff(c_5391,plain,(
    v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_80])).

tff(c_5380,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_5286])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_62,plain,(
    ! [B_43,C_44] :
      ( k1_relset_1(k1_xboole_0,B_43,C_44) = k1_xboole_0
      | ~ v1_funct_2(C_44,k1_xboole_0,B_43)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_83,plain,(
    ! [B_43,C_44] :
      ( k1_relset_1(k1_xboole_0,B_43,C_44) = k1_xboole_0
      | ~ v1_funct_2(C_44,k1_xboole_0,B_43)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_6648,plain,(
    ! [B_584,C_585] :
      ( k1_relset_1('#skF_3',B_584,C_585) = '#skF_3'
      | ~ v1_funct_2(C_585,'#skF_3',B_584)
      | ~ m1_subset_1(C_585,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5380,c_5380,c_5380,c_5380,c_83])).

tff(c_6653,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5391,c_6648])).

tff(c_6660,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5382,c_6494,c_6653])).

tff(c_5388,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_177])).

tff(c_5568,plain,(
    ! [A_463] :
      ( k2_relat_1(k2_funct_1(A_463)) = k1_relat_1(A_463)
      | ~ v2_funct_1(A_463)
      | ~ v1_funct_1(A_463)
      | ~ v1_relat_1(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8729,plain,(
    ! [A_731] :
      ( v1_funct_2(k2_funct_1(A_731),k1_relat_1(k2_funct_1(A_731)),k1_relat_1(A_731))
      | ~ v1_funct_1(k2_funct_1(A_731))
      | ~ v1_relat_1(k2_funct_1(A_731))
      | ~ v2_funct_1(A_731)
      | ~ v1_funct_1(A_731)
      | ~ v1_relat_1(A_731) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5568,c_68])).

tff(c_8744,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6660,c_8729])).

tff(c_8760,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k1_relat_1(k2_funct_1('#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5389,c_5393,c_5392,c_5388,c_8744])).

tff(c_8761,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8760])).

tff(c_8764,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_8761])).

tff(c_8768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5389,c_5393,c_8764])).

tff(c_8770,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_8760])).

tff(c_5294,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_24])).

tff(c_5378,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_5375,c_5294])).

tff(c_6495,plain,(
    ! [A_573,B_574,C_575] :
      ( k2_relset_1(A_573,B_574,C_575) = k2_relat_1(C_575)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_6566,plain,(
    ! [B_580,C_581] :
      ( k2_relset_1('#skF_3',B_580,C_581) = k2_relat_1(C_581)
      | ~ m1_subset_1(C_581,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5378,c_6495])).

tff(c_6574,plain,(
    ! [B_582] : k2_relset_1('#skF_3',B_582,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5382,c_6566])).

tff(c_5390,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5375,c_74])).

tff(c_6578,plain,(
    k2_relat_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6574,c_5390])).

tff(c_6147,plain,(
    ! [A_510] :
      ( m1_subset_1(A_510,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_510),k2_relat_1(A_510))))
      | ~ v1_funct_1(A_510)
      | ~ v1_relat_1(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9045,plain,(
    ! [A_743] :
      ( m1_subset_1(k2_funct_1(A_743),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_743),k2_relat_1(k2_funct_1(A_743)))))
      | ~ v1_funct_1(k2_funct_1(A_743))
      | ~ v1_relat_1(k2_funct_1(A_743))
      | ~ v2_funct_1(A_743)
      | ~ v1_funct_1(A_743)
      | ~ v1_relat_1(A_743) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_6147])).

tff(c_9090,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6578,c_9045])).

tff(c_9116,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k2_relat_1(k2_funct_1('#skF_3'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5389,c_5393,c_5392,c_8770,c_5388,c_9090])).

tff(c_9149,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_relat_1('#skF_3'))))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9116])).

tff(c_9171,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5389,c_5393,c_5392,c_5377,c_6660,c_9149])).

tff(c_9173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5516,c_9171])).

tff(c_9174,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5374])).

tff(c_9178,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_9174,c_5294])).

tff(c_9187,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_204])).

tff(c_9298,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9178,c_9187])).

tff(c_9189,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_167])).

tff(c_9193,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_82])).

tff(c_9192,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_76])).

tff(c_9188,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_177])).

tff(c_9182,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_9174,c_5224])).

tff(c_9958,plain,(
    ! [A_808,B_809,C_810] :
      ( k1_relset_1(A_808,B_809,C_810) = k1_relat_1(C_810)
      | ~ m1_subset_1(C_810,k1_zfmisc_1(k2_zfmisc_1(A_808,B_809))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_10151,plain,(
    ! [B_844,C_845] :
      ( k1_relset_1('#skF_4',B_844,C_845) = k1_relat_1(C_845)
      | ~ m1_subset_1(C_845,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9178,c_9958])).

tff(c_10157,plain,(
    ! [B_844] : k1_relset_1('#skF_4',B_844,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9182,c_10151])).

tff(c_9180,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_5286])).

tff(c_58,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_84,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_58])).

tff(c_10350,plain,(
    ! [C_867,B_868] :
      ( v1_funct_2(C_867,'#skF_4',B_868)
      | k1_relset_1('#skF_4',B_868,C_867) != '#skF_4'
      | ~ m1_subset_1(C_867,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_9180,c_9180,c_9180,c_84])).

tff(c_10352,plain,(
    ! [B_868] :
      ( v1_funct_2('#skF_4','#skF_4',B_868)
      | k1_relset_1('#skF_4',B_868,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_9182,c_10350])).

tff(c_10357,plain,(
    ! [B_868] :
      ( v1_funct_2('#skF_4','#skF_4',B_868)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10157,c_10352])).

tff(c_10389,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_10357])).

tff(c_9183,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_5247])).

tff(c_9376,plain,(
    ! [C_759,A_760,B_761] :
      ( v1_partfun1(C_759,A_760)
      | ~ m1_subset_1(C_759,k1_zfmisc_1(k2_zfmisc_1(A_760,B_761)))
      | ~ v1_xboole_0(A_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_9379,plain,(
    ! [C_759] :
      ( v1_partfun1(C_759,'#skF_4')
      | ~ m1_subset_1(C_759,k1_zfmisc_1('#skF_4'))
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9178,c_9376])).

tff(c_9390,plain,(
    ! [C_762] :
      ( v1_partfun1(C_762,'#skF_4')
      | ~ m1_subset_1(C_762,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9183,c_9379])).

tff(c_9398,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_9182,c_9390])).

tff(c_11057,plain,(
    ! [A_918,B_919,A_920] :
      ( k1_relset_1(A_918,B_919,A_920) = k1_relat_1(A_920)
      | ~ r1_tarski(A_920,k2_zfmisc_1(A_918,B_919)) ) ),
    inference(resolution,[status(thm)],[c_28,c_9958])).

tff(c_11090,plain,(
    ! [A_921,B_922,A_923] :
      ( k1_relset_1(A_921,B_922,A_923) = k1_relat_1(A_923)
      | ~ v1_xboole_0(A_923) ) ),
    inference(resolution,[status(thm)],[c_188,c_11057])).

tff(c_11099,plain,(
    ! [A_921,B_922] : k1_relset_1(A_921,B_922,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9183,c_11090])).

tff(c_9177,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_9174,c_5295])).

tff(c_10184,plain,(
    ! [A_849,B_850,C_851] :
      ( k2_relset_1(A_849,B_850,C_851) = k2_relat_1(C_851)
      | ~ m1_subset_1(C_851,k1_zfmisc_1(k2_zfmisc_1(A_849,B_850))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10301,plain,(
    ! [A_864,C_865] :
      ( k2_relset_1(A_864,'#skF_4',C_865) = k2_relat_1(C_865)
      | ~ m1_subset_1(C_865,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9177,c_10184])).

tff(c_10309,plain,(
    ! [A_866] : k2_relset_1(A_866,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_9182,c_10301])).

tff(c_9190,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9174,c_74])).

tff(c_10316,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_10309,c_9190])).

tff(c_10076,plain,(
    ! [A_832] :
      ( m1_subset_1(A_832,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_832),k2_relat_1(A_832))))
      | ~ v1_funct_1(A_832)
      | ~ v1_relat_1(A_832) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10106,plain,(
    ! [A_832] :
      ( r1_tarski(A_832,k2_zfmisc_1(k1_relat_1(A_832),k2_relat_1(A_832)))
      | ~ v1_funct_1(A_832)
      | ~ v1_relat_1(A_832) ) ),
    inference(resolution,[status(thm)],[c_10076,c_26])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5240,plain,(
    ! [C_437,B_438,A_439] :
      ( r2_hidden(C_437,B_438)
      | ~ r2_hidden(C_437,A_439)
      | ~ r1_tarski(A_439,B_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10973,plain,(
    ! [A_908,B_909,B_910] :
      ( r2_hidden('#skF_2'(A_908,B_909),B_910)
      | ~ r1_tarski(A_908,B_910)
      | r1_tarski(A_908,B_909) ) ),
    inference(resolution,[status(thm)],[c_10,c_5240])).

tff(c_10986,plain,(
    ! [B_911,A_912,B_913] :
      ( ~ v1_xboole_0(B_911)
      | ~ r1_tarski(A_912,B_911)
      | r1_tarski(A_912,B_913) ) ),
    inference(resolution,[status(thm)],[c_10973,c_2])).

tff(c_12617,plain,(
    ! [A_1028,B_1029] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_1028),k2_relat_1(A_1028)))
      | r1_tarski(A_1028,B_1029)
      | ~ v1_funct_1(A_1028)
      | ~ v1_relat_1(A_1028) ) ),
    inference(resolution,[status(thm)],[c_10106,c_10986])).

tff(c_12635,plain,(
    ! [B_1029] :
      ( ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_4'))
      | r1_tarski('#skF_4',B_1029)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10316,c_12617])).

tff(c_12666,plain,(
    ! [B_1030] : r1_tarski('#skF_4',B_1030) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9189,c_9193,c_9183,c_9177,c_12635])).

tff(c_10882,plain,(
    ! [C_904,A_905,B_906] :
      ( v1_funct_2(C_904,A_905,B_906)
      | ~ v1_partfun1(C_904,A_905)
      | ~ v1_funct_1(C_904)
      | ~ m1_subset_1(C_904,k1_zfmisc_1(k2_zfmisc_1(A_905,B_906))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10909,plain,(
    ! [A_14,A_905,B_906] :
      ( v1_funct_2(A_14,A_905,B_906)
      | ~ v1_partfun1(A_14,A_905)
      | ~ v1_funct_1(A_14)
      | ~ r1_tarski(A_14,k2_zfmisc_1(A_905,B_906)) ) ),
    inference(resolution,[status(thm)],[c_28,c_10882])).

tff(c_12670,plain,(
    ! [A_905,B_906] :
      ( v1_funct_2('#skF_4',A_905,B_906)
      | ~ v1_partfun1('#skF_4',A_905)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12666,c_10909])).

tff(c_12778,plain,(
    ! [A_1032,B_1033] :
      ( v1_funct_2('#skF_4',A_1032,B_1033)
      | ~ v1_partfun1('#skF_4',A_1032) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9193,c_12670])).

tff(c_10440,plain,(
    ! [B_43,C_44] :
      ( k1_relset_1('#skF_4',B_43,C_44) = '#skF_4'
      | ~ v1_funct_2(C_44,'#skF_4',B_43)
      | ~ m1_subset_1(C_44,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9180,c_9180,c_9180,c_9180,c_83])).

tff(c_12781,plain,(
    ! [B_1033] :
      ( k1_relset_1('#skF_4',B_1033,'#skF_4') = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_partfun1('#skF_4','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12778,c_10440])).

tff(c_12787,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9398,c_9182,c_11099,c_12781])).

tff(c_12789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10389,c_12787])).

tff(c_12791,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10357])).

tff(c_9442,plain,(
    ! [A_769] :
      ( k2_relat_1(k2_funct_1(A_769)) = k1_relat_1(A_769)
      | ~ v2_funct_1(A_769)
      | ~ v1_funct_1(A_769)
      | ~ v1_relat_1(A_769) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14860,plain,(
    ! [A_1156] :
      ( v1_funct_2(k2_funct_1(A_1156),k1_relat_1(k2_funct_1(A_1156)),k1_relat_1(A_1156))
      | ~ v1_funct_1(k2_funct_1(A_1156))
      | ~ v1_relat_1(k2_funct_1(A_1156))
      | ~ v2_funct_1(A_1156)
      | ~ v1_funct_1(A_1156)
      | ~ v1_relat_1(A_1156) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9442,c_68])).

tff(c_14875,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12791,c_14860])).

tff(c_14891,plain,
    ( v1_funct_2(k2_funct_1('#skF_4'),k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9189,c_9193,c_9192,c_9188,c_14875])).

tff(c_14892,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_14891])).

tff(c_14895,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_14892])).

tff(c_14899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9189,c_9193,c_14895])).

tff(c_14901,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_14891])).

tff(c_15108,plain,(
    ! [A_1193] :
      ( m1_subset_1(k2_funct_1(A_1193),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1193)),k1_relat_1(A_1193))))
      | ~ v1_funct_1(k2_funct_1(A_1193))
      | ~ v1_relat_1(k2_funct_1(A_1193))
      | ~ v2_funct_1(A_1193)
      | ~ v1_funct_1(A_1193)
      | ~ v1_relat_1(A_1193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10076])).

tff(c_15153,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')),'#skF_4')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12791,c_15108])).

tff(c_15179,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9189,c_9193,c_9192,c_14901,c_9188,c_9177,c_15153])).

tff(c_15181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9298,c_15179])).

tff(c_15183,plain,(
    m1_subset_1(k2_funct_1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_16834,plain,(
    ! [C_1342,A_1343,B_1344] :
      ( v1_xboole_0(C_1342)
      | ~ m1_subset_1(C_1342,k1_zfmisc_1(k2_zfmisc_1(A_1343,B_1344)))
      | ~ v1_xboole_0(A_1343) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_16853,plain,
    ( v1_xboole_0(k2_funct_1('#skF_5'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_15183,c_16834])).

tff(c_16855,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_16853])).

tff(c_15306,plain,(
    ! [C_1214,A_1215,B_1216] :
      ( v1_xboole_0(C_1214)
      | ~ m1_subset_1(C_1214,k1_zfmisc_1(k2_zfmisc_1(A_1215,B_1216)))
      | ~ v1_xboole_0(A_1215) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_15325,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_15306])).

tff(c_15328,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_15325])).

tff(c_16053,plain,(
    ! [A_1279,B_1280,C_1281] :
      ( k2_relset_1(A_1279,B_1280,C_1281) = k2_relat_1(C_1281)
      | ~ m1_subset_1(C_1281,k1_zfmisc_1(k2_zfmisc_1(A_1279,B_1280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16078,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_16053])).

tff(c_16089,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_16078])).

tff(c_15182,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_16131,plain,(
    ! [A_1282,B_1283,C_1284] :
      ( k1_relset_1(A_1282,B_1283,C_1284) = k1_relat_1(C_1284)
      | ~ m1_subset_1(C_1284,k1_zfmisc_1(k2_zfmisc_1(A_1282,B_1283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_16168,plain,(
    k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) = k1_relat_1(k2_funct_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_15183,c_16131])).

tff(c_16527,plain,(
    ! [B_1329,C_1330,A_1331] :
      ( k1_xboole_0 = B_1329
      | v1_funct_2(C_1330,A_1331,B_1329)
      | k1_relset_1(A_1331,B_1329,C_1330) != A_1331
      | ~ m1_subset_1(C_1330,k1_zfmisc_1(k2_zfmisc_1(A_1331,B_1329))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_16548,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relset_1('#skF_4','#skF_3',k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_15183,c_16527])).

tff(c_16567,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_funct_1('#skF_5'),'#skF_4','#skF_3')
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16168,c_16548])).

tff(c_16568,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_15182,c_16567])).

tff(c_16573,plain,(
    k1_relat_1(k2_funct_1('#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16568])).

tff(c_16576,plain,
    ( k2_relat_1('#skF_5') != '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_16573])).

tff(c_16579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_82,c_76,c_16089,c_16576])).

tff(c_16580,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_16568])).

tff(c_16624,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16580,c_12])).

tff(c_16626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15328,c_16624])).

tff(c_16628,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_15325])).

tff(c_15233,plain,(
    ! [B_1200,A_1201] :
      ( B_1200 = A_1201
      | ~ r1_tarski(B_1200,A_1201)
      | ~ v1_xboole_0(A_1201) ) ),
    inference(resolution,[status(thm)],[c_189,c_14])).

tff(c_15258,plain,(
    ! [B_1204,A_1205] :
      ( B_1204 = A_1205
      | ~ v1_xboole_0(B_1204)
      | ~ v1_xboole_0(A_1205) ) ),
    inference(resolution,[status(thm)],[c_188,c_15233])).

tff(c_15261,plain,(
    ! [A_1205] :
      ( k1_xboole_0 = A_1205
      | ~ v1_xboole_0(A_1205) ) ),
    inference(resolution,[status(thm)],[c_12,c_15258])).

tff(c_16649,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16628,c_15261])).

tff(c_16627,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_15325])).

tff(c_16637,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16627,c_15261])).

tff(c_16666,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16649,c_16637])).

tff(c_16657,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16637,c_16637,c_24])).

tff(c_16717,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16666,c_16666,c_16657])).

tff(c_15248,plain,
    ( k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_126,c_15233])).

tff(c_15268,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_15248])).

tff(c_16718,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16717,c_15268])).

tff(c_16721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16628,c_16718])).

tff(c_16722,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15248])).

tff(c_16723,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_15248])).

tff(c_16748,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16722,c_16723])).

tff(c_16757,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16748,c_15261])).

tff(c_16743,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_16722,c_20])).

tff(c_16859,plain,
    ( '#skF_5' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16757,c_16757,c_16757,c_16743])).

tff(c_16860,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_16859])).

tff(c_16732,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16722,c_78])).

tff(c_16865,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_16860,c_16732])).

tff(c_16866,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_16757])).

tff(c_54,plain,(
    ! [A_42] :
      ( v1_funct_2(k1_xboole_0,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_42,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_85,plain,(
    ! [A_42] :
      ( v1_funct_2(k1_xboole_0,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_54])).

tff(c_16887,plain,(
    ! [A_42] :
      ( v1_funct_2('#skF_3',A_42,'#skF_3')
      | A_42 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16866,c_16866,c_16866,c_16866,c_16866,c_85])).

tff(c_16888,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_16887])).

tff(c_16910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16865,c_16888])).

tff(c_17107,plain,(
    ! [A_1357] :
      ( v1_funct_2('#skF_3',A_1357,'#skF_3')
      | A_1357 = '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_16887])).

tff(c_16867,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_16748])).

tff(c_16767,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16757,c_16757,c_22])).

tff(c_16862,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_16860,c_16767])).

tff(c_16871,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_15183])).

tff(c_17025,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16862,c_16871])).

tff(c_17029,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_17025,c_26])).

tff(c_192,plain,(
    ! [B_69,A_68] :
      ( B_69 = A_68
      | ~ r1_tarski(B_69,A_68)
      | ~ v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_189,c_14])).

tff(c_17035,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_17029,c_192])).

tff(c_17042,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16867,c_17035])).

tff(c_16872,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16860,c_15182])).

tff(c_17046,plain,(
    ~ v1_funct_2('#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17042,c_16872])).

tff(c_17111,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17107,c_17046])).

tff(c_17127,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_16867])).

tff(c_17131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16855,c_17127])).

tff(c_17132,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_16859])).

tff(c_17140,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17132,c_16748])).

tff(c_17153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16855,c_17140])).

tff(c_17155,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_16853])).

tff(c_15247,plain,(
    ! [B_67,A_66] :
      ( B_67 = A_66
      | ~ v1_xboole_0(B_67)
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_188,c_15233])).

tff(c_16758,plain,(
    ! [A_66] :
      ( A_66 = '#skF_5'
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_16748,c_15247])).

tff(c_17164,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17155,c_16758])).

tff(c_17175,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_17164,c_16732])).

tff(c_16766,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_5',B_13) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16757,c_16757,c_24])).

tff(c_17173,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_17164,c_16766])).

tff(c_17468,plain,(
    ! [A_1380,B_1381,C_1382] :
      ( k1_relset_1(A_1380,B_1381,C_1382) = k1_relat_1(C_1382)
      | ~ m1_subset_1(C_1382,k1_zfmisc_1(k2_zfmisc_1(A_1380,B_1381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18351,plain,(
    ! [B_1471,C_1472] :
      ( k1_relset_1('#skF_4',B_1471,C_1472) = k1_relat_1(C_1472)
      | ~ m1_subset_1(C_1472,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17173,c_17468])).

tff(c_18357,plain,(
    ! [B_1471] : k1_relset_1('#skF_4',B_1471,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17175,c_18351])).

tff(c_17176,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_16757])).

tff(c_18385,plain,(
    ! [C_1476,B_1477] :
      ( v1_funct_2(C_1476,'#skF_4',B_1477)
      | k1_relset_1('#skF_4',B_1477,C_1476) != '#skF_4'
      | ~ m1_subset_1(C_1476,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17176,c_17176,c_17176,c_17176,c_84])).

tff(c_18387,plain,(
    ! [B_1477] :
      ( v1_funct_2('#skF_4','#skF_4',B_1477)
      | k1_relset_1('#skF_4',B_1477,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_17175,c_18385])).

tff(c_18392,plain,(
    ! [B_1477] :
      ( v1_funct_2('#skF_4','#skF_4',B_1477)
      | k1_relat_1('#skF_4') != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18357,c_18387])).

tff(c_18394,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18392])).

tff(c_178,plain,(
    ! [C_65] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_154])).

tff(c_193,plain,(
    ! [A_70] :
      ( v1_relat_1(A_70)
      | ~ r1_tarski(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_178])).

tff(c_202,plain,(
    ! [A_66] :
      ( v1_relat_1(A_66)
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_188,c_193])).

tff(c_17166,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17155,c_202])).

tff(c_17188,plain,(
    v1_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_82])).

tff(c_17187,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_76])).

tff(c_17154,plain,(
    v1_xboole_0(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_16853])).

tff(c_17199,plain,(
    v1_xboole_0(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_17154])).

tff(c_17208,plain,(
    ! [A_1359] :
      ( A_1359 = '#skF_4'
      | ~ v1_xboole_0(A_1359) ) ),
    inference(resolution,[status(thm)],[c_17155,c_15247])).

tff(c_17215,plain,(
    k2_funct_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17199,c_17208])).

tff(c_17340,plain,(
    ! [A_1367] :
      ( k2_relat_1(k2_funct_1(A_1367)) = k1_relat_1(A_1367)
      | ~ v2_funct_1(A_1367)
      | ~ v1_funct_1(A_1367)
      | ~ v1_relat_1(A_1367) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_17352,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17215,c_17340])).

tff(c_17356,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17166,c_17188,c_17187,c_17352])).

tff(c_17172,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_17164,c_16767])).

tff(c_18027,plain,(
    ! [A_1426,B_1427,C_1428] :
      ( k2_relset_1(A_1426,B_1427,C_1428) = k2_relat_1(C_1428)
      | ~ m1_subset_1(C_1428,k1_zfmisc_1(k2_zfmisc_1(A_1426,B_1427))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18448,plain,(
    ! [A_1483,C_1484] :
      ( k2_relset_1(A_1483,'#skF_4',C_1484) = k2_relat_1(C_1484)
      | ~ m1_subset_1(C_1484,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17172,c_18027])).

tff(c_18450,plain,(
    ! [A_1483] : k2_relset_1(A_1483,'#skF_4','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_17175,c_18448])).

tff(c_18457,plain,(
    ! [A_1485] : k2_relset_1(A_1485,'#skF_4','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17356,c_18450])).

tff(c_17185,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_74])).

tff(c_18464,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18457,c_17185])).

tff(c_18475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18394,c_18464])).

tff(c_18476,plain,(
    ! [B_1477] : v1_funct_2('#skF_4','#skF_4',B_1477) ),
    inference(splitRight,[status(thm)],[c_18392])).

tff(c_17182,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17164,c_15182])).

tff(c_17333,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17215,c_17182])).

tff(c_18529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18476,c_17333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:56:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.14/3.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.14/3.82  
% 10.14/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.14/3.82  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 10.14/3.82  
% 10.14/3.82  %Foreground sorts:
% 10.14/3.82  
% 10.14/3.82  
% 10.14/3.82  %Background operators:
% 10.14/3.82  
% 10.14/3.82  
% 10.14/3.82  %Foreground operators:
% 10.14/3.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.14/3.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.14/3.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.14/3.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.14/3.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.14/3.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.14/3.82  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.14/3.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.14/3.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.14/3.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.14/3.82  tff('#skF_5', type, '#skF_5': $i).
% 10.14/3.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.14/3.82  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.14/3.82  tff('#skF_3', type, '#skF_3': $i).
% 10.14/3.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.14/3.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.14/3.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.14/3.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.14/3.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.14/3.82  tff('#skF_4', type, '#skF_4': $i).
% 10.14/3.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.14/3.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.14/3.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.14/3.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.14/3.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.14/3.82  
% 10.51/3.86  tff(f_161, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 10.51/3.86  tff(f_91, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 10.51/3.86  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.51/3.86  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.51/3.86  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.51/3.86  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 10.51/3.86  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 10.51/3.86  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.51/3.86  tff(f_144, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 10.51/3.86  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.51/3.86  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.51/3.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.51/3.86  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.51/3.86  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.51/3.86  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.51/3.86  tff(f_116, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 10.51/3.86  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 10.51/3.86  tff(f_84, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 10.51/3.86  tff(c_78, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.51/3.86  tff(c_494, plain, (![C_111, B_112, A_113]: (v1_xboole_0(C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(B_112, A_113))) | ~v1_xboole_0(A_113))), inference(cnfTransformation, [status(thm)], [f_91])).
% 10.51/3.86  tff(c_512, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_78, c_494])).
% 10.51/3.86  tff(c_527, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_512])).
% 10.51/3.86  tff(c_154, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.51/3.86  tff(c_167, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_154])).
% 10.51/3.86  tff(c_82, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.51/3.86  tff(c_30, plain, (![A_16]: (v1_funct_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.86  tff(c_72, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.51/3.86  tff(c_168, plain, (~v1_funct_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_72])).
% 10.51/3.86  tff(c_171, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_168])).
% 10.51/3.86  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_82, c_171])).
% 10.51/3.86  tff(c_176, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | ~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_72])).
% 10.51/3.86  tff(c_204, plain, (~m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_176])).
% 10.51/3.86  tff(c_76, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.51/3.86  tff(c_80, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.51/3.86  tff(c_996, plain, (![A_147, B_148, C_149]: (k1_relset_1(A_147, B_148, C_149)=k1_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.51/3.86  tff(c_1027, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_996])).
% 10.51/3.86  tff(c_1573, plain, (![B_219, A_220, C_221]: (k1_xboole_0=B_219 | k1_relset_1(A_220, B_219, C_221)=A_220 | ~v1_funct_2(C_221, A_220, B_219) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.51/3.86  tff(c_1598, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_78, c_1573])).
% 10.51/3.86  tff(c_1612, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1027, c_1598])).
% 10.51/3.86  tff(c_1614, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1612])).
% 10.51/3.86  tff(c_34, plain, (![A_17]: (k2_relat_1(k2_funct_1(A_17))=k1_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.51/3.86  tff(c_32, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.51/3.86  tff(c_177, plain, (v1_funct_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_72])).
% 10.51/3.86  tff(c_74, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_161])).
% 10.51/3.86  tff(c_1044, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.51/3.86  tff(c_1066, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_1044])).
% 10.51/3.86  tff(c_1076, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1066])).
% 10.51/3.86  tff(c_515, plain, (![A_114]: (k1_relat_1(k2_funct_1(A_114))=k2_relat_1(A_114) | ~v2_funct_1(A_114) | ~v1_funct_1(A_114) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.51/3.86  tff(c_68, plain, (![A_45]: (v1_funct_2(A_45, k1_relat_1(A_45), k2_relat_1(A_45)) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.51/3.86  tff(c_4192, plain, (![A_392]: (v1_funct_2(k2_funct_1(A_392), k2_relat_1(A_392), k2_relat_1(k2_funct_1(A_392))) | ~v1_funct_1(k2_funct_1(A_392)) | ~v1_relat_1(k2_funct_1(A_392)) | ~v2_funct_1(A_392) | ~v1_funct_1(A_392) | ~v1_relat_1(A_392))), inference(superposition, [status(thm), theory('equality')], [c_515, c_68])).
% 10.51/3.86  tff(c_4210, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1076, c_4192])).
% 10.51/3.86  tff(c_4227, plain, (v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', k2_relat_1(k2_funct_1('#skF_5'))) | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_82, c_76, c_177, c_4210])).
% 10.51/3.86  tff(c_4228, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4227])).
% 10.51/3.86  tff(c_4231, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_4228])).
% 10.51/3.86  tff(c_4235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_82, c_4231])).
% 10.51/3.86  tff(c_4237, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4227])).
% 10.51/3.86  tff(c_36, plain, (![A_17]: (k1_relat_1(k2_funct_1(A_17))=k2_relat_1(A_17) | ~v2_funct_1(A_17) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.51/3.86  tff(c_839, plain, (![A_137]: (m1_subset_1(A_137, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_137), k2_relat_1(A_137)))) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.51/3.86  tff(c_4910, plain, (![A_431]: (m1_subset_1(k2_funct_1(A_431), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_431), k2_relat_1(k2_funct_1(A_431))))) | ~v1_funct_1(k2_funct_1(A_431)) | ~v1_relat_1(k2_funct_1(A_431)) | ~v2_funct_1(A_431) | ~v1_funct_1(A_431) | ~v1_relat_1(A_431))), inference(superposition, [status(thm), theory('equality')], [c_36, c_839])).
% 10.51/3.86  tff(c_4955, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5'))))) | ~v1_funct_1(k2_funct_1('#skF_5')) | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1076, c_4910])).
% 10.51/3.86  tff(c_4981, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_82, c_76, c_4237, c_177, c_4955])).
% 10.51/3.86  tff(c_5014, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_5')))) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_34, c_4981])).
% 10.51/3.86  tff(c_5035, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_82, c_76, c_1614, c_5014])).
% 10.51/3.86  tff(c_5037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_5035])).
% 10.51/3.86  tff(c_5038, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1612])).
% 10.51/3.86  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.51/3.86  tff(c_5083, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5038, c_12])).
% 10.51/3.86  tff(c_5085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_527, c_5083])).
% 10.51/3.86  tff(c_5087, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_512])).
% 10.51/3.86  tff(c_184, plain, (![A_66, B_67]: (r2_hidden('#skF_2'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.51/3.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.51/3.86  tff(c_188, plain, (![A_66, B_67]: (~v1_xboole_0(A_66) | r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_184, c_2])).
% 10.51/3.86  tff(c_189, plain, (![A_68, B_69]: (~v1_xboole_0(A_68) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_184, c_2])).
% 10.51/3.86  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.51/3.86  tff(c_253, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_189, c_14])).
% 10.51/3.86  tff(c_268, plain, (![B_81, A_82]: (B_81=A_82 | ~v1_xboole_0(B_81) | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_188, c_253])).
% 10.51/3.86  tff(c_271, plain, (![A_82]: (k1_xboole_0=A_82 | ~v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_12, c_268])).
% 10.51/3.86  tff(c_5120, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_5087, c_271])).
% 10.51/3.86  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.51/3.86  tff(c_5135, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5120, c_5120, c_22])).
% 10.51/3.86  tff(c_122, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | ~m1_subset_1(A_53, k1_zfmisc_1(B_54)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.51/3.86  tff(c_126, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_122])).
% 10.51/3.86  tff(c_264, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_253])).
% 10.51/3.86  tff(c_267, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_264])).
% 10.51/3.86  tff(c_5217, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5135, c_267])).
% 10.51/3.86  tff(c_5220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5087, c_5217])).
% 10.51/3.86  tff(c_5221, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_264])).
% 10.51/3.86  tff(c_5222, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_264])).
% 10.51/3.86  tff(c_5247, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_5222])).
% 10.51/3.86  tff(c_5272, plain, (![B_441, A_442]: (B_441=A_442 | ~v1_xboole_0(B_441) | ~v1_xboole_0(A_442))), inference(resolution, [status(thm)], [c_188, c_253])).
% 10.51/3.86  tff(c_5279, plain, (![A_443]: (k1_xboole_0=A_443 | ~v1_xboole_0(A_443))), inference(resolution, [status(thm)], [c_12, c_5272])).
% 10.51/3.86  tff(c_5286, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_5247, c_5279])).
% 10.51/3.86  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.51/3.86  tff(c_5235, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5221, c_20])).
% 10.51/3.86  tff(c_5374, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_5286, c_5235])).
% 10.51/3.86  tff(c_5375, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_5374])).
% 10.51/3.86  tff(c_5295, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_22])).
% 10.51/3.86  tff(c_5377, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_5375, c_5295])).
% 10.51/3.86  tff(c_5387, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_204])).
% 10.51/3.86  tff(c_5516, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5377, c_5387])).
% 10.51/3.86  tff(c_5389, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_167])).
% 10.51/3.86  tff(c_5393, plain, (v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_82])).
% 10.51/3.86  tff(c_5392, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_76])).
% 10.51/3.86  tff(c_5224, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_78])).
% 10.51/3.86  tff(c_5382, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_5375, c_5224])).
% 10.51/3.86  tff(c_5383, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_5247])).
% 10.51/3.86  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.51/3.86  tff(c_6248, plain, (![A_527, B_528, C_529]: (k1_relset_1(A_527, B_528, C_529)=k1_relat_1(C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_527, B_528))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.51/3.86  tff(c_6456, plain, (![A_567, B_568, A_569]: (k1_relset_1(A_567, B_568, A_569)=k1_relat_1(A_569) | ~r1_tarski(A_569, k2_zfmisc_1(A_567, B_568)))), inference(resolution, [status(thm)], [c_28, c_6248])).
% 10.51/3.86  tff(c_6485, plain, (![A_570, B_571, A_572]: (k1_relset_1(A_570, B_571, A_572)=k1_relat_1(A_572) | ~v1_xboole_0(A_572))), inference(resolution, [status(thm)], [c_188, c_6456])).
% 10.51/3.86  tff(c_6494, plain, (![A_570, B_571]: (k1_relset_1(A_570, B_571, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5383, c_6485])).
% 10.51/3.86  tff(c_5391, plain, (v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_80])).
% 10.51/3.86  tff(c_5380, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_5286])).
% 10.51/3.86  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.51/3.86  tff(c_62, plain, (![B_43, C_44]: (k1_relset_1(k1_xboole_0, B_43, C_44)=k1_xboole_0 | ~v1_funct_2(C_44, k1_xboole_0, B_43) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_43))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.51/3.86  tff(c_83, plain, (![B_43, C_44]: (k1_relset_1(k1_xboole_0, B_43, C_44)=k1_xboole_0 | ~v1_funct_2(C_44, k1_xboole_0, B_43) | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_62])).
% 10.51/3.86  tff(c_6648, plain, (![B_584, C_585]: (k1_relset_1('#skF_3', B_584, C_585)='#skF_3' | ~v1_funct_2(C_585, '#skF_3', B_584) | ~m1_subset_1(C_585, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5380, c_5380, c_5380, c_5380, c_83])).
% 10.51/3.86  tff(c_6653, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_5391, c_6648])).
% 10.51/3.86  tff(c_6660, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5382, c_6494, c_6653])).
% 10.51/3.86  tff(c_5388, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_177])).
% 10.51/3.86  tff(c_5568, plain, (![A_463]: (k2_relat_1(k2_funct_1(A_463))=k1_relat_1(A_463) | ~v2_funct_1(A_463) | ~v1_funct_1(A_463) | ~v1_relat_1(A_463))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.51/3.86  tff(c_8729, plain, (![A_731]: (v1_funct_2(k2_funct_1(A_731), k1_relat_1(k2_funct_1(A_731)), k1_relat_1(A_731)) | ~v1_funct_1(k2_funct_1(A_731)) | ~v1_relat_1(k2_funct_1(A_731)) | ~v2_funct_1(A_731) | ~v1_funct_1(A_731) | ~v1_relat_1(A_731))), inference(superposition, [status(thm), theory('equality')], [c_5568, c_68])).
% 10.51/3.86  tff(c_8744, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6660, c_8729])).
% 10.51/3.86  tff(c_8760, plain, (v1_funct_2(k2_funct_1('#skF_3'), k1_relat_1(k2_funct_1('#skF_3')), '#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5389, c_5393, c_5392, c_5388, c_8744])).
% 10.51/3.86  tff(c_8761, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_8760])).
% 10.51/3.86  tff(c_8764, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_8761])).
% 10.51/3.86  tff(c_8768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5389, c_5393, c_8764])).
% 10.51/3.86  tff(c_8770, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_8760])).
% 10.51/3.86  tff(c_5294, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_24])).
% 10.51/3.86  tff(c_5378, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_5375, c_5294])).
% 10.51/3.86  tff(c_6495, plain, (![A_573, B_574, C_575]: (k2_relset_1(A_573, B_574, C_575)=k2_relat_1(C_575) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.51/3.86  tff(c_6566, plain, (![B_580, C_581]: (k2_relset_1('#skF_3', B_580, C_581)=k2_relat_1(C_581) | ~m1_subset_1(C_581, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5378, c_6495])).
% 10.51/3.86  tff(c_6574, plain, (![B_582]: (k2_relset_1('#skF_3', B_582, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5382, c_6566])).
% 10.51/3.86  tff(c_5390, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5375, c_74])).
% 10.51/3.86  tff(c_6578, plain, (k2_relat_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6574, c_5390])).
% 10.51/3.86  tff(c_6147, plain, (![A_510]: (m1_subset_1(A_510, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_510), k2_relat_1(A_510)))) | ~v1_funct_1(A_510) | ~v1_relat_1(A_510))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.51/3.86  tff(c_9045, plain, (![A_743]: (m1_subset_1(k2_funct_1(A_743), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_743), k2_relat_1(k2_funct_1(A_743))))) | ~v1_funct_1(k2_funct_1(A_743)) | ~v1_relat_1(k2_funct_1(A_743)) | ~v2_funct_1(A_743) | ~v1_funct_1(A_743) | ~v1_relat_1(A_743))), inference(superposition, [status(thm), theory('equality')], [c_36, c_6147])).
% 10.51/3.86  tff(c_9090, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6578, c_9045])).
% 10.51/3.86  tff(c_9116, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k2_relat_1(k2_funct_1('#skF_3')))))), inference(demodulation, [status(thm), theory('equality')], [c_5389, c_5393, c_5392, c_8770, c_5388, c_9090])).
% 10.51/3.86  tff(c_9149, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_relat_1('#skF_3')))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_9116])).
% 10.51/3.86  tff(c_9171, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5389, c_5393, c_5392, c_5377, c_6660, c_9149])).
% 10.51/3.86  tff(c_9173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5516, c_9171])).
% 10.51/3.86  tff(c_9174, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_5374])).
% 10.51/3.86  tff(c_9178, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_9174, c_5294])).
% 10.51/3.86  tff(c_9187, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_204])).
% 10.51/3.86  tff(c_9298, plain, (~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9178, c_9187])).
% 10.51/3.86  tff(c_9189, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_167])).
% 10.51/3.86  tff(c_9193, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_82])).
% 10.51/3.86  tff(c_9192, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_76])).
% 10.51/3.86  tff(c_9188, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_177])).
% 10.51/3.86  tff(c_9182, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_9174, c_5224])).
% 10.51/3.86  tff(c_9958, plain, (![A_808, B_809, C_810]: (k1_relset_1(A_808, B_809, C_810)=k1_relat_1(C_810) | ~m1_subset_1(C_810, k1_zfmisc_1(k2_zfmisc_1(A_808, B_809))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.51/3.86  tff(c_10151, plain, (![B_844, C_845]: (k1_relset_1('#skF_4', B_844, C_845)=k1_relat_1(C_845) | ~m1_subset_1(C_845, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9178, c_9958])).
% 10.51/3.86  tff(c_10157, plain, (![B_844]: (k1_relset_1('#skF_4', B_844, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9182, c_10151])).
% 10.51/3.86  tff(c_9180, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_5286])).
% 10.51/3.86  tff(c_58, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_43))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.51/3.86  tff(c_84, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_58])).
% 10.51/3.86  tff(c_10350, plain, (![C_867, B_868]: (v1_funct_2(C_867, '#skF_4', B_868) | k1_relset_1('#skF_4', B_868, C_867)!='#skF_4' | ~m1_subset_1(C_867, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_9180, c_9180, c_9180, c_84])).
% 10.51/3.86  tff(c_10352, plain, (![B_868]: (v1_funct_2('#skF_4', '#skF_4', B_868) | k1_relset_1('#skF_4', B_868, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_9182, c_10350])).
% 10.51/3.86  tff(c_10357, plain, (![B_868]: (v1_funct_2('#skF_4', '#skF_4', B_868) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10157, c_10352])).
% 10.51/3.86  tff(c_10389, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_10357])).
% 10.51/3.86  tff(c_9183, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_5247])).
% 10.51/3.86  tff(c_9376, plain, (![C_759, A_760, B_761]: (v1_partfun1(C_759, A_760) | ~m1_subset_1(C_759, k1_zfmisc_1(k2_zfmisc_1(A_760, B_761))) | ~v1_xboole_0(A_760))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.51/3.86  tff(c_9379, plain, (![C_759]: (v1_partfun1(C_759, '#skF_4') | ~m1_subset_1(C_759, k1_zfmisc_1('#skF_4')) | ~v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9178, c_9376])).
% 10.51/3.86  tff(c_9390, plain, (![C_762]: (v1_partfun1(C_762, '#skF_4') | ~m1_subset_1(C_762, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9183, c_9379])).
% 10.51/3.86  tff(c_9398, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_9182, c_9390])).
% 10.51/3.86  tff(c_11057, plain, (![A_918, B_919, A_920]: (k1_relset_1(A_918, B_919, A_920)=k1_relat_1(A_920) | ~r1_tarski(A_920, k2_zfmisc_1(A_918, B_919)))), inference(resolution, [status(thm)], [c_28, c_9958])).
% 10.51/3.86  tff(c_11090, plain, (![A_921, B_922, A_923]: (k1_relset_1(A_921, B_922, A_923)=k1_relat_1(A_923) | ~v1_xboole_0(A_923))), inference(resolution, [status(thm)], [c_188, c_11057])).
% 10.51/3.86  tff(c_11099, plain, (![A_921, B_922]: (k1_relset_1(A_921, B_922, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9183, c_11090])).
% 10.51/3.86  tff(c_9177, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_9174, c_5295])).
% 10.51/3.86  tff(c_10184, plain, (![A_849, B_850, C_851]: (k2_relset_1(A_849, B_850, C_851)=k2_relat_1(C_851) | ~m1_subset_1(C_851, k1_zfmisc_1(k2_zfmisc_1(A_849, B_850))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.51/3.86  tff(c_10301, plain, (![A_864, C_865]: (k2_relset_1(A_864, '#skF_4', C_865)=k2_relat_1(C_865) | ~m1_subset_1(C_865, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9177, c_10184])).
% 10.51/3.86  tff(c_10309, plain, (![A_866]: (k2_relset_1(A_866, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_9182, c_10301])).
% 10.51/3.86  tff(c_9190, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9174, c_74])).
% 10.51/3.86  tff(c_10316, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_10309, c_9190])).
% 10.51/3.86  tff(c_10076, plain, (![A_832]: (m1_subset_1(A_832, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_832), k2_relat_1(A_832)))) | ~v1_funct_1(A_832) | ~v1_relat_1(A_832))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.51/3.86  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.51/3.86  tff(c_10106, plain, (![A_832]: (r1_tarski(A_832, k2_zfmisc_1(k1_relat_1(A_832), k2_relat_1(A_832))) | ~v1_funct_1(A_832) | ~v1_relat_1(A_832))), inference(resolution, [status(thm)], [c_10076, c_26])).
% 10.51/3.86  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.51/3.86  tff(c_5240, plain, (![C_437, B_438, A_439]: (r2_hidden(C_437, B_438) | ~r2_hidden(C_437, A_439) | ~r1_tarski(A_439, B_438))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.51/3.86  tff(c_10973, plain, (![A_908, B_909, B_910]: (r2_hidden('#skF_2'(A_908, B_909), B_910) | ~r1_tarski(A_908, B_910) | r1_tarski(A_908, B_909))), inference(resolution, [status(thm)], [c_10, c_5240])).
% 10.51/3.86  tff(c_10986, plain, (![B_911, A_912, B_913]: (~v1_xboole_0(B_911) | ~r1_tarski(A_912, B_911) | r1_tarski(A_912, B_913))), inference(resolution, [status(thm)], [c_10973, c_2])).
% 10.51/3.86  tff(c_12617, plain, (![A_1028, B_1029]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1(A_1028), k2_relat_1(A_1028))) | r1_tarski(A_1028, B_1029) | ~v1_funct_1(A_1028) | ~v1_relat_1(A_1028))), inference(resolution, [status(thm)], [c_10106, c_10986])).
% 10.51/3.86  tff(c_12635, plain, (![B_1029]: (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_4')) | r1_tarski('#skF_4', B_1029) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10316, c_12617])).
% 10.51/3.86  tff(c_12666, plain, (![B_1030]: (r1_tarski('#skF_4', B_1030))), inference(demodulation, [status(thm), theory('equality')], [c_9189, c_9193, c_9183, c_9177, c_12635])).
% 10.51/3.86  tff(c_10882, plain, (![C_904, A_905, B_906]: (v1_funct_2(C_904, A_905, B_906) | ~v1_partfun1(C_904, A_905) | ~v1_funct_1(C_904) | ~m1_subset_1(C_904, k1_zfmisc_1(k2_zfmisc_1(A_905, B_906))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.51/3.86  tff(c_10909, plain, (![A_14, A_905, B_906]: (v1_funct_2(A_14, A_905, B_906) | ~v1_partfun1(A_14, A_905) | ~v1_funct_1(A_14) | ~r1_tarski(A_14, k2_zfmisc_1(A_905, B_906)))), inference(resolution, [status(thm)], [c_28, c_10882])).
% 10.51/3.86  tff(c_12670, plain, (![A_905, B_906]: (v1_funct_2('#skF_4', A_905, B_906) | ~v1_partfun1('#skF_4', A_905) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12666, c_10909])).
% 10.51/3.86  tff(c_12778, plain, (![A_1032, B_1033]: (v1_funct_2('#skF_4', A_1032, B_1033) | ~v1_partfun1('#skF_4', A_1032))), inference(demodulation, [status(thm), theory('equality')], [c_9193, c_12670])).
% 10.51/3.86  tff(c_10440, plain, (![B_43, C_44]: (k1_relset_1('#skF_4', B_43, C_44)='#skF_4' | ~v1_funct_2(C_44, '#skF_4', B_43) | ~m1_subset_1(C_44, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9180, c_9180, c_9180, c_9180, c_83])).
% 10.51/3.86  tff(c_12781, plain, (![B_1033]: (k1_relset_1('#skF_4', B_1033, '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_partfun1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_12778, c_10440])).
% 10.51/3.86  tff(c_12787, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9398, c_9182, c_11099, c_12781])).
% 10.51/3.86  tff(c_12789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10389, c_12787])).
% 10.51/3.86  tff(c_12791, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_10357])).
% 10.51/3.86  tff(c_9442, plain, (![A_769]: (k2_relat_1(k2_funct_1(A_769))=k1_relat_1(A_769) | ~v2_funct_1(A_769) | ~v1_funct_1(A_769) | ~v1_relat_1(A_769))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.51/3.86  tff(c_14860, plain, (![A_1156]: (v1_funct_2(k2_funct_1(A_1156), k1_relat_1(k2_funct_1(A_1156)), k1_relat_1(A_1156)) | ~v1_funct_1(k2_funct_1(A_1156)) | ~v1_relat_1(k2_funct_1(A_1156)) | ~v2_funct_1(A_1156) | ~v1_funct_1(A_1156) | ~v1_relat_1(A_1156))), inference(superposition, [status(thm), theory('equality')], [c_9442, c_68])).
% 10.51/3.86  tff(c_14875, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12791, c_14860])).
% 10.51/3.86  tff(c_14891, plain, (v1_funct_2(k2_funct_1('#skF_4'), k1_relat_1(k2_funct_1('#skF_4')), '#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9189, c_9193, c_9192, c_9188, c_14875])).
% 10.51/3.86  tff(c_14892, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_14891])).
% 10.51/3.86  tff(c_14895, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_14892])).
% 10.51/3.86  tff(c_14899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9189, c_9193, c_14895])).
% 10.51/3.86  tff(c_14901, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_14891])).
% 10.51/3.86  tff(c_15108, plain, (![A_1193]: (m1_subset_1(k2_funct_1(A_1193), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(A_1193)), k1_relat_1(A_1193)))) | ~v1_funct_1(k2_funct_1(A_1193)) | ~v1_relat_1(k2_funct_1(A_1193)) | ~v2_funct_1(A_1193) | ~v1_funct_1(A_1193) | ~v1_relat_1(A_1193))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10076])).
% 10.51/3.86  tff(c_15153, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_4')), '#skF_4'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12791, c_15108])).
% 10.51/3.86  tff(c_15179, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9189, c_9193, c_9192, c_14901, c_9188, c_9177, c_15153])).
% 10.51/3.86  tff(c_15181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9298, c_15179])).
% 10.51/3.86  tff(c_15183, plain, (m1_subset_1(k2_funct_1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_176])).
% 10.51/3.86  tff(c_16834, plain, (![C_1342, A_1343, B_1344]: (v1_xboole_0(C_1342) | ~m1_subset_1(C_1342, k1_zfmisc_1(k2_zfmisc_1(A_1343, B_1344))) | ~v1_xboole_0(A_1343))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.51/3.86  tff(c_16853, plain, (v1_xboole_0(k2_funct_1('#skF_5')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_15183, c_16834])).
% 10.51/3.86  tff(c_16855, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_16853])).
% 10.51/3.86  tff(c_15306, plain, (![C_1214, A_1215, B_1216]: (v1_xboole_0(C_1214) | ~m1_subset_1(C_1214, k1_zfmisc_1(k2_zfmisc_1(A_1215, B_1216))) | ~v1_xboole_0(A_1215))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.51/3.86  tff(c_15325, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_78, c_15306])).
% 10.51/3.86  tff(c_15328, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_15325])).
% 10.51/3.86  tff(c_16053, plain, (![A_1279, B_1280, C_1281]: (k2_relset_1(A_1279, B_1280, C_1281)=k2_relat_1(C_1281) | ~m1_subset_1(C_1281, k1_zfmisc_1(k2_zfmisc_1(A_1279, B_1280))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.51/3.86  tff(c_16078, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_16053])).
% 10.51/3.86  tff(c_16089, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_16078])).
% 10.51/3.86  tff(c_15182, plain, (~v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_176])).
% 10.51/3.86  tff(c_16131, plain, (![A_1282, B_1283, C_1284]: (k1_relset_1(A_1282, B_1283, C_1284)=k1_relat_1(C_1284) | ~m1_subset_1(C_1284, k1_zfmisc_1(k2_zfmisc_1(A_1282, B_1283))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.51/3.86  tff(c_16168, plain, (k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))=k1_relat_1(k2_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_15183, c_16131])).
% 10.51/3.86  tff(c_16527, plain, (![B_1329, C_1330, A_1331]: (k1_xboole_0=B_1329 | v1_funct_2(C_1330, A_1331, B_1329) | k1_relset_1(A_1331, B_1329, C_1330)!=A_1331 | ~m1_subset_1(C_1330, k1_zfmisc_1(k2_zfmisc_1(A_1331, B_1329))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.51/3.86  tff(c_16548, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relset_1('#skF_4', '#skF_3', k2_funct_1('#skF_5'))!='#skF_4'), inference(resolution, [status(thm)], [c_15183, c_16527])).
% 10.51/3.86  tff(c_16567, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_funct_1('#skF_5'), '#skF_4', '#skF_3') | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16168, c_16548])).
% 10.51/3.86  tff(c_16568, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_15182, c_16567])).
% 10.51/3.86  tff(c_16573, plain, (k1_relat_1(k2_funct_1('#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_16568])).
% 10.51/3.86  tff(c_16576, plain, (k2_relat_1('#skF_5')!='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_36, c_16573])).
% 10.51/3.86  tff(c_16579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_82, c_76, c_16089, c_16576])).
% 10.51/3.86  tff(c_16580, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_16568])).
% 10.51/3.86  tff(c_16624, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16580, c_12])).
% 10.51/3.86  tff(c_16626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15328, c_16624])).
% 10.51/3.86  tff(c_16628, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_15325])).
% 10.51/3.86  tff(c_15233, plain, (![B_1200, A_1201]: (B_1200=A_1201 | ~r1_tarski(B_1200, A_1201) | ~v1_xboole_0(A_1201))), inference(resolution, [status(thm)], [c_189, c_14])).
% 10.51/3.86  tff(c_15258, plain, (![B_1204, A_1205]: (B_1204=A_1205 | ~v1_xboole_0(B_1204) | ~v1_xboole_0(A_1205))), inference(resolution, [status(thm)], [c_188, c_15233])).
% 10.51/3.86  tff(c_15261, plain, (![A_1205]: (k1_xboole_0=A_1205 | ~v1_xboole_0(A_1205))), inference(resolution, [status(thm)], [c_12, c_15258])).
% 10.51/3.86  tff(c_16649, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_16628, c_15261])).
% 10.51/3.86  tff(c_16627, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_15325])).
% 10.51/3.86  tff(c_16637, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_16627, c_15261])).
% 10.51/3.86  tff(c_16666, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16649, c_16637])).
% 10.51/3.86  tff(c_16657, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16637, c_16637, c_24])).
% 10.51/3.86  tff(c_16717, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16666, c_16666, c_16657])).
% 10.51/3.86  tff(c_15248, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5' | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_126, c_15233])).
% 10.51/3.86  tff(c_15268, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_15248])).
% 10.51/3.86  tff(c_16718, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16717, c_15268])).
% 10.51/3.86  tff(c_16721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16628, c_16718])).
% 10.51/3.86  tff(c_16722, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_15248])).
% 10.51/3.86  tff(c_16723, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_15248])).
% 10.51/3.86  tff(c_16748, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16722, c_16723])).
% 10.51/3.86  tff(c_16757, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_16748, c_15261])).
% 10.51/3.86  tff(c_16743, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_16722, c_20])).
% 10.51/3.86  tff(c_16859, plain, ('#skF_5'='#skF_4' | '#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16757, c_16757, c_16757, c_16743])).
% 10.51/3.86  tff(c_16860, plain, ('#skF_5'='#skF_3'), inference(splitLeft, [status(thm)], [c_16859])).
% 10.51/3.86  tff(c_16732, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_16722, c_78])).
% 10.51/3.86  tff(c_16865, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16860, c_16860, c_16732])).
% 10.51/3.86  tff(c_16866, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16860, c_16757])).
% 10.51/3.86  tff(c_54, plain, (![A_42]: (v1_funct_2(k1_xboole_0, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_42, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.51/3.86  tff(c_85, plain, (![A_42]: (v1_funct_2(k1_xboole_0, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_54])).
% 10.51/3.86  tff(c_16887, plain, (![A_42]: (v1_funct_2('#skF_3', A_42, '#skF_3') | A_42='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16866, c_16866, c_16866, c_16866, c_16866, c_85])).
% 10.51/3.86  tff(c_16888, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_16887])).
% 10.51/3.86  tff(c_16910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16865, c_16888])).
% 10.51/3.86  tff(c_17107, plain, (![A_1357]: (v1_funct_2('#skF_3', A_1357, '#skF_3') | A_1357='#skF_3')), inference(splitRight, [status(thm)], [c_16887])).
% 10.51/3.86  tff(c_16867, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16860, c_16748])).
% 10.51/3.86  tff(c_16767, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16757, c_16757, c_22])).
% 10.51/3.86  tff(c_16862, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16860, c_16860, c_16767])).
% 10.51/3.86  tff(c_16871, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16860, c_15183])).
% 10.51/3.86  tff(c_17025, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_16862, c_16871])).
% 10.51/3.86  tff(c_17029, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_17025, c_26])).
% 10.51/3.86  tff(c_192, plain, (![B_69, A_68]: (B_69=A_68 | ~r1_tarski(B_69, A_68) | ~v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_189, c_14])).
% 10.51/3.86  tff(c_17035, plain, (k2_funct_1('#skF_3')='#skF_3' | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_17029, c_192])).
% 10.51/3.86  tff(c_17042, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16867, c_17035])).
% 10.51/3.86  tff(c_16872, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16860, c_15182])).
% 10.51/3.86  tff(c_17046, plain, (~v1_funct_2('#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17042, c_16872])).
% 10.51/3.86  tff(c_17111, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_17107, c_17046])).
% 10.51/3.86  tff(c_17127, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_16867])).
% 10.51/3.86  tff(c_17131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16855, c_17127])).
% 10.51/3.86  tff(c_17132, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_16859])).
% 10.51/3.86  tff(c_17140, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17132, c_16748])).
% 10.51/3.86  tff(c_17153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16855, c_17140])).
% 10.51/3.86  tff(c_17155, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_16853])).
% 10.51/3.86  tff(c_15247, plain, (![B_67, A_66]: (B_67=A_66 | ~v1_xboole_0(B_67) | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_188, c_15233])).
% 10.51/3.86  tff(c_16758, plain, (![A_66]: (A_66='#skF_5' | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_16748, c_15247])).
% 10.51/3.86  tff(c_17164, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_17155, c_16758])).
% 10.51/3.86  tff(c_17175, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_17164, c_16732])).
% 10.51/3.86  tff(c_16766, plain, (![B_13]: (k2_zfmisc_1('#skF_5', B_13)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16757, c_16757, c_24])).
% 10.51/3.86  tff(c_17173, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_17164, c_16766])).
% 10.51/3.86  tff(c_17468, plain, (![A_1380, B_1381, C_1382]: (k1_relset_1(A_1380, B_1381, C_1382)=k1_relat_1(C_1382) | ~m1_subset_1(C_1382, k1_zfmisc_1(k2_zfmisc_1(A_1380, B_1381))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 10.51/3.86  tff(c_18351, plain, (![B_1471, C_1472]: (k1_relset_1('#skF_4', B_1471, C_1472)=k1_relat_1(C_1472) | ~m1_subset_1(C_1472, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_17173, c_17468])).
% 10.51/3.86  tff(c_18357, plain, (![B_1471]: (k1_relset_1('#skF_4', B_1471, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_17175, c_18351])).
% 10.51/3.86  tff(c_17176, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_16757])).
% 10.51/3.86  tff(c_18385, plain, (![C_1476, B_1477]: (v1_funct_2(C_1476, '#skF_4', B_1477) | k1_relset_1('#skF_4', B_1477, C_1476)!='#skF_4' | ~m1_subset_1(C_1476, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_17176, c_17176, c_17176, c_17176, c_84])).
% 10.51/3.86  tff(c_18387, plain, (![B_1477]: (v1_funct_2('#skF_4', '#skF_4', B_1477) | k1_relset_1('#skF_4', B_1477, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_17175, c_18385])).
% 10.51/3.86  tff(c_18392, plain, (![B_1477]: (v1_funct_2('#skF_4', '#skF_4', B_1477) | k1_relat_1('#skF_4')!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18357, c_18387])).
% 10.51/3.86  tff(c_18394, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_18392])).
% 10.51/3.86  tff(c_178, plain, (![C_65]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_154])).
% 10.51/3.86  tff(c_193, plain, (![A_70]: (v1_relat_1(A_70) | ~r1_tarski(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_178])).
% 10.51/3.86  tff(c_202, plain, (![A_66]: (v1_relat_1(A_66) | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_188, c_193])).
% 10.51/3.86  tff(c_17166, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_17155, c_202])).
% 10.51/3.86  tff(c_17188, plain, (v1_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_82])).
% 10.51/3.86  tff(c_17187, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_76])).
% 10.51/3.86  tff(c_17154, plain, (v1_xboole_0(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_16853])).
% 10.51/3.86  tff(c_17199, plain, (v1_xboole_0(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_17154])).
% 10.51/3.86  tff(c_17208, plain, (![A_1359]: (A_1359='#skF_4' | ~v1_xboole_0(A_1359))), inference(resolution, [status(thm)], [c_17155, c_15247])).
% 10.51/3.86  tff(c_17215, plain, (k2_funct_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_17199, c_17208])).
% 10.51/3.86  tff(c_17340, plain, (![A_1367]: (k2_relat_1(k2_funct_1(A_1367))=k1_relat_1(A_1367) | ~v2_funct_1(A_1367) | ~v1_funct_1(A_1367) | ~v1_relat_1(A_1367))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.51/3.86  tff(c_17352, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17215, c_17340])).
% 10.51/3.86  tff(c_17356, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17166, c_17188, c_17187, c_17352])).
% 10.51/3.86  tff(c_17172, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_17164, c_16767])).
% 10.51/3.86  tff(c_18027, plain, (![A_1426, B_1427, C_1428]: (k2_relset_1(A_1426, B_1427, C_1428)=k2_relat_1(C_1428) | ~m1_subset_1(C_1428, k1_zfmisc_1(k2_zfmisc_1(A_1426, B_1427))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 10.51/3.86  tff(c_18448, plain, (![A_1483, C_1484]: (k2_relset_1(A_1483, '#skF_4', C_1484)=k2_relat_1(C_1484) | ~m1_subset_1(C_1484, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_17172, c_18027])).
% 10.51/3.86  tff(c_18450, plain, (![A_1483]: (k2_relset_1(A_1483, '#skF_4', '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_17175, c_18448])).
% 10.51/3.86  tff(c_18457, plain, (![A_1485]: (k2_relset_1(A_1485, '#skF_4', '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17356, c_18450])).
% 10.51/3.86  tff(c_17185, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_74])).
% 10.51/3.86  tff(c_18464, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18457, c_17185])).
% 10.51/3.86  tff(c_18475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18394, c_18464])).
% 10.51/3.86  tff(c_18476, plain, (![B_1477]: (v1_funct_2('#skF_4', '#skF_4', B_1477))), inference(splitRight, [status(thm)], [c_18392])).
% 10.51/3.86  tff(c_17182, plain, (~v1_funct_2(k2_funct_1('#skF_4'), '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17164, c_15182])).
% 10.51/3.86  tff(c_17333, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17215, c_17182])).
% 10.51/3.86  tff(c_18529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18476, c_17333])).
% 10.51/3.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.51/3.86  
% 10.51/3.86  Inference rules
% 10.51/3.86  ----------------------
% 10.51/3.86  #Ref     : 0
% 10.51/3.86  #Sup     : 4277
% 10.51/3.86  #Fact    : 0
% 10.51/3.86  #Define  : 0
% 10.51/3.86  #Split   : 38
% 10.51/3.86  #Chain   : 0
% 10.51/3.86  #Close   : 0
% 10.51/3.86  
% 10.51/3.86  Ordering : KBO
% 10.51/3.86  
% 10.51/3.86  Simplification rules
% 10.51/3.86  ----------------------
% 10.51/3.86  #Subsume      : 913
% 10.51/3.86  #Demod        : 3210
% 10.51/3.86  #Tautology    : 2137
% 10.51/3.86  #SimpNegUnit  : 36
% 10.51/3.86  #BackRed      : 381
% 10.51/3.86  
% 10.51/3.86  #Partial instantiations: 0
% 10.51/3.86  #Strategies tried      : 1
% 10.51/3.86  
% 10.51/3.86  Timing (in seconds)
% 10.51/3.86  ----------------------
% 10.51/3.87  Preprocessing        : 0.37
% 10.51/3.87  Parsing              : 0.20
% 10.51/3.87  CNF conversion       : 0.02
% 10.51/3.87  Main loop            : 2.60
% 10.51/3.87  Inferencing          : 0.82
% 10.51/3.87  Reduction            : 0.82
% 10.51/3.87  Demodulation         : 0.56
% 10.51/3.87  BG Simplification    : 0.09
% 10.51/3.87  Subsumption          : 0.67
% 10.51/3.87  Abstraction          : 0.11
% 10.51/3.87  MUC search           : 0.00
% 10.51/3.87  Cooper               : 0.00
% 10.51/3.87  Total                : 3.08
% 10.51/3.87  Index Insertion      : 0.00
% 10.51/3.87  Index Deletion       : 0.00
% 10.51/3.87  Index Matching       : 0.00
% 10.51/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
