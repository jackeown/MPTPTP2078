%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:53 EST 2020

% Result     : Theorem 17.29s
% Output     : CNFRefutation 17.29s
% Verified   : 
% Statistics : Number of formulae       :  122 (1229 expanded)
%              Number of leaves         :   40 ( 461 expanded)
%              Depth                    :   34
%              Number of atoms          :  333 (4301 expanded)
%              Number of equality atoms :   63 ( 947 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(D)
            & r2_hidden(C,A) )
         => ( B = k1_xboole_0
            | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => ( v2_funct_1(C)
        <=> ! [D,E] :
              ( ( r2_hidden(D,A)
                & r2_hidden(E,A)
                & k1_funct_1(C,D) = k1_funct_1(C,E) )
             => D = E ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_2)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_72,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_66,plain,(
    r2_hidden('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_74,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_83,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k7_relset_1(A_74,B_75,C_76,D_77) = k9_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_86,plain,(
    ! [D_77] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_77) = k9_relat_1('#skF_10',D_77) ),
    inference(resolution,[status(thm)],[c_70,c_83])).

tff(c_104,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_relset_1(A_82,B_83,C_84,A_82) = k2_relset_1(A_82,B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_106,plain,(
    k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_7') = k2_relset_1('#skF_7','#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_104])).

tff(c_108,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_10') = k9_relat_1('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_106])).

tff(c_229,plain,(
    ! [D_128,C_129,A_130,B_131] :
      ( r2_hidden(k1_funct_1(D_128,C_129),k2_relset_1(A_130,B_131,D_128))
      | k1_xboole_0 = B_131
      | ~ r2_hidden(C_129,A_130)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_2(D_128,A_130,B_131)
      | ~ v1_funct_1(D_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_241,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_10',C_129),k9_relat_1('#skF_10','#skF_7'))
      | k1_xboole_0 = '#skF_8'
      | ~ r2_hidden(C_129,'#skF_7')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_10','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_229])).

tff(c_246,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_10',C_129),k9_relat_1('#skF_10','#skF_7'))
      | k1_xboole_0 = '#skF_8'
      | ~ r2_hidden(C_129,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_241])).

tff(c_247,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_10',C_129),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(C_129,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_246])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_70,c_76])).

tff(c_82,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_68,plain,(
    v2_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12,plain,(
    ! [A_6,B_29,D_44] :
      ( r2_hidden('#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44),k1_relat_1(A_6))
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_6,B_29,D_44] :
      ( r2_hidden('#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44),B_29)
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_6,B_29,D_44] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44)) = D_44
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [B_49,A_48] :
      ( k1_funct_1(k2_funct_1(B_49),k1_funct_1(B_49,A_48)) = A_48
      | ~ r2_hidden(A_48,k1_relat_1(B_49))
      | ~ v2_funct_1(B_49)
      | ~ v1_funct_1(B_49)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_155,plain,(
    ! [A_98,B_99,D_100] :
      ( k1_funct_1(A_98,'#skF_4'(A_98,B_99,k9_relat_1(A_98,B_99),D_100)) = D_100
      | ~ r2_hidden(D_100,k9_relat_1(A_98,B_99))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_365,plain,(
    ! [A_170,D_171,B_172] :
      ( k1_funct_1(k2_funct_1(A_170),D_171) = '#skF_4'(A_170,B_172,k9_relat_1(A_170,B_172),D_171)
      | ~ r2_hidden('#skF_4'(A_170,B_172,k9_relat_1(A_170,B_172),D_171),k1_relat_1(A_170))
      | ~ v2_funct_1(A_170)
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170)
      | ~ r2_hidden(D_171,k9_relat_1(A_170,B_172))
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_32])).

tff(c_375,plain,(
    ! [A_173,D_174,B_175] :
      ( k1_funct_1(k2_funct_1(A_173),D_174) = '#skF_4'(A_173,B_175,k9_relat_1(A_173,B_175),D_174)
      | ~ v2_funct_1(A_173)
      | ~ r2_hidden(D_174,k9_relat_1(A_173,B_175))
      | ~ v1_funct_1(A_173)
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_12,c_365])).

tff(c_377,plain,(
    ! [C_129] :
      ( k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_129)) = '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',C_129))
      | ~ v2_funct_1('#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_129,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_247,c_375])).

tff(c_404,plain,(
    ! [C_176] :
      ( k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_176)) = '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',C_176))
      | ~ r2_hidden(C_176,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_68,c_377])).

tff(c_450,plain,(
    ! [B_29,D_44] :
      ( '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10','#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44))) = k1_funct_1(k2_funct_1('#skF_10'),D_44)
      | ~ r2_hidden('#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10',B_29))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_404])).

tff(c_17424,plain,(
    ! [B_538,D_539] :
      ( '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10','#skF_4'('#skF_10',B_538,k9_relat_1('#skF_10',B_538),D_539))) = k1_funct_1(k2_funct_1('#skF_10'),D_539)
      | ~ r2_hidden('#skF_4'('#skF_10',B_538,k9_relat_1('#skF_10',B_538),D_539),'#skF_7')
      | ~ r2_hidden(D_539,k9_relat_1('#skF_10',B_538)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_450])).

tff(c_17551,plain,(
    ! [D_539,B_538] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),D_539),'#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_10','#skF_4'('#skF_10',B_538,k9_relat_1('#skF_10',B_538),D_539)),k9_relat_1('#skF_10','#skF_7'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden('#skF_4'('#skF_10',B_538,k9_relat_1('#skF_10',B_538),D_539),'#skF_7')
      | ~ r2_hidden(D_539,k9_relat_1('#skF_10',B_538)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17424,c_10])).

tff(c_19527,plain,(
    ! [D_574,B_575] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),D_574),'#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_10','#skF_4'('#skF_10',B_575,k9_relat_1('#skF_10',B_575),D_574)),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_10',B_575,k9_relat_1('#skF_10',B_575),D_574),'#skF_7')
      | ~ r2_hidden(D_574,k9_relat_1('#skF_10',B_575)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_17551])).

tff(c_19647,plain,(
    ! [D_576,B_577] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),D_576),'#skF_7')
      | ~ r2_hidden(D_576,k9_relat_1('#skF_10',B_577))
      | ~ r2_hidden('#skF_4'('#skF_10',B_577,k9_relat_1('#skF_10',B_577),D_576),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_247,c_19527])).

tff(c_19696,plain,(
    ! [D_44] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10','#skF_7'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_10,c_19647])).

tff(c_19711,plain,(
    ! [D_578] :
      ( r2_hidden(k1_funct_1(k2_funct_1('#skF_10'),D_578),'#skF_7')
      | ~ r2_hidden(D_578,k9_relat_1('#skF_10','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_19696])).

tff(c_19785,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,'#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_10',A_48),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(A_48,k1_relat_1('#skF_10'))
      | ~ v2_funct_1('#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_19711])).

tff(c_19806,plain,(
    ! [A_579] :
      ( r2_hidden(A_579,'#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_10',A_579),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(A_579,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_68,c_19785])).

tff(c_19865,plain,(
    ! [B_29,D_44] :
      ( r2_hidden('#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10',B_29))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_19806])).

tff(c_21097,plain,(
    ! [B_608,D_609] :
      ( r2_hidden('#skF_4'('#skF_10',B_608,k9_relat_1('#skF_10',B_608),D_609),'#skF_7')
      | ~ r2_hidden(D_609,k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_10',B_608,k9_relat_1('#skF_10',B_608),D_609),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_609,k9_relat_1('#skF_10',B_608)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_19865])).

tff(c_21203,plain,(
    ! [B_29,D_44] :
      ( r2_hidden('#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10',B_29))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_12,c_21097])).

tff(c_21237,plain,(
    ! [B_610,D_611] :
      ( r2_hidden('#skF_4'('#skF_10',B_610,k9_relat_1('#skF_10',B_610),D_611),'#skF_7')
      | ~ r2_hidden(D_611,k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(D_611,k9_relat_1('#skF_10',B_610)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_21203])).

tff(c_397,plain,(
    ! [C_129] :
      ( k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_129)) = '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',C_129))
      | ~ r2_hidden(C_129,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_68,c_377])).

tff(c_6,plain,(
    ! [A_6,E_47,B_29] :
      ( r2_hidden(k1_funct_1(A_6,E_47),k9_relat_1(A_6,B_29))
      | ~ r2_hidden(E_47,B_29)
      | ~ r2_hidden(E_47,k1_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_614,plain,(
    ! [D_181,A_182,B_183,B_184] :
      ( r2_hidden(D_181,k9_relat_1(A_182,B_183))
      | ~ r2_hidden('#skF_4'(A_182,B_184,k9_relat_1(A_182,B_184),D_181),B_183)
      | ~ r2_hidden('#skF_4'(A_182,B_184,k9_relat_1(A_182,B_184),D_181),k1_relat_1(A_182))
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182)
      | ~ r2_hidden(D_181,k9_relat_1(A_182,B_184))
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_6])).

tff(c_627,plain,(
    ! [D_185,A_186,B_187] :
      ( r2_hidden(D_185,k9_relat_1(A_186,k1_relat_1(A_186)))
      | ~ r2_hidden('#skF_4'(A_186,B_187,k9_relat_1(A_186,B_187),D_185),k1_relat_1(A_186))
      | ~ r2_hidden(D_185,k9_relat_1(A_186,B_187))
      | ~ v1_funct_1(A_186)
      | ~ v1_relat_1(A_186) ) ),
    inference(resolution,[status(thm)],[c_12,c_614])).

tff(c_645,plain,(
    ! [D_188,A_189,B_190] :
      ( r2_hidden(D_188,k9_relat_1(A_189,k1_relat_1(A_189)))
      | ~ r2_hidden(D_188,k9_relat_1(A_189,B_190))
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_12,c_627])).

tff(c_647,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_10',C_129),k9_relat_1('#skF_10',k1_relat_1('#skF_10')))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_129,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_247,c_645])).

tff(c_667,plain,(
    ! [C_129] :
      ( r2_hidden(k1_funct_1('#skF_10',C_129),k9_relat_1('#skF_10',k1_relat_1('#skF_10')))
      | ~ r2_hidden(C_129,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_647])).

tff(c_674,plain,(
    ! [C_191] :
      ( r2_hidden(k1_funct_1('#skF_10',C_191),k9_relat_1('#skF_10',k1_relat_1('#skF_10')))
      | ~ r2_hidden(C_191,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_647])).

tff(c_373,plain,(
    ! [A_6,D_44,B_29] :
      ( k1_funct_1(k2_funct_1(A_6),D_44) = '#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44)
      | ~ v2_funct_1(A_6)
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_365])).

tff(c_678,plain,(
    ! [C_191] :
      ( '#skF_4'('#skF_10',k1_relat_1('#skF_10'),k9_relat_1('#skF_10',k1_relat_1('#skF_10')),k1_funct_1('#skF_10',C_191)) = k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_191))
      | ~ v2_funct_1('#skF_10')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_191,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_674,c_373])).

tff(c_745,plain,(
    ! [C_196] :
      ( '#skF_4'('#skF_10',k1_relat_1('#skF_10'),k9_relat_1('#skF_10',k1_relat_1('#skF_10')),k1_funct_1('#skF_10',C_196)) = k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_196))
      | ~ r2_hidden(C_196,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_68,c_678])).

tff(c_759,plain,(
    ! [C_196] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_196))) = k1_funct_1('#skF_10',C_196)
      | ~ r2_hidden(k1_funct_1('#skF_10',C_196),k9_relat_1('#skF_10',k1_relat_1('#skF_10')))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_196,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_8])).

tff(c_1296,plain,(
    ! [C_216] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_216))) = k1_funct_1('#skF_10',C_216)
      | ~ r2_hidden(k1_funct_1('#skF_10',C_216),k9_relat_1('#skF_10',k1_relat_1('#skF_10')))
      | ~ r2_hidden(C_216,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_759])).

tff(c_1344,plain,(
    ! [C_217] :
      ( k1_funct_1('#skF_10',k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10',C_217))) = k1_funct_1('#skF_10',C_217)
      | ~ r2_hidden(C_217,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_667,c_1296])).

tff(c_1486,plain,(
    ! [C_218] :
      ( k1_funct_1('#skF_10','#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',C_218))) = k1_funct_1('#skF_10',C_218)
      | ~ r2_hidden(C_218,'#skF_7')
      | ~ r2_hidden(C_218,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_1344])).

tff(c_1577,plain,(
    ! [B_29,D_44] :
      ( k1_funct_1('#skF_10','#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44)) = k1_funct_1('#skF_10','#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_44))
      | ~ r2_hidden('#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10',B_29))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1486])).

tff(c_1621,plain,(
    ! [B_29,D_44] :
      ( k1_funct_1('#skF_10','#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44)) = k1_funct_1('#skF_10','#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_44))
      | ~ r2_hidden('#skF_4'('#skF_10',B_29,k9_relat_1('#skF_10',B_29),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10',B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_1577])).

tff(c_24932,plain,(
    ! [B_642,D_643] :
      ( k1_funct_1('#skF_10','#skF_4'('#skF_10',B_642,k9_relat_1('#skF_10',B_642),D_643)) = k1_funct_1('#skF_10','#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_643))
      | ~ r2_hidden(D_643,k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(D_643,k9_relat_1('#skF_10',B_642)) ) ),
    inference(resolution,[status(thm)],[c_21237,c_1621])).

tff(c_26503,plain,(
    ! [D_652,B_653] :
      ( r2_hidden(k1_funct_1('#skF_10','#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_652)),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden('#skF_4'('#skF_10',B_653,k9_relat_1('#skF_10',B_653),D_652),'#skF_7')
      | ~ r2_hidden(D_652,k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(D_652,k9_relat_1('#skF_10',B_653)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24932,c_247])).

tff(c_26560,plain,(
    ! [D_44] :
      ( r2_hidden(k1_funct_1('#skF_10','#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_44)),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10','#skF_7'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_10,c_26503])).

tff(c_26578,plain,(
    ! [D_654] :
      ( r2_hidden(k1_funct_1('#skF_10','#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_654)),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(D_654,k9_relat_1('#skF_10','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_26560])).

tff(c_19805,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,'#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_10',A_48),k9_relat_1('#skF_10','#skF_7'))
      | ~ r2_hidden(A_48,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_68,c_19785])).

tff(c_26703,plain,(
    ! [D_655] :
      ( r2_hidden('#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_655),'#skF_7')
      | ~ r2_hidden('#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_655),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_655,k9_relat_1('#skF_10','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_26578,c_19805])).

tff(c_26791,plain,(
    ! [D_44] :
      ( r2_hidden('#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10','#skF_7'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_12,c_26703])).

tff(c_26810,plain,(
    ! [D_44] :
      ( r2_hidden('#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),D_44),'#skF_7')
      | ~ r2_hidden(D_44,k9_relat_1('#skF_10','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_26791])).

tff(c_317,plain,(
    ! [C_160,D_157,E_159,B_156,A_158] :
      ( k1_xboole_0 = B_156
      | E_159 = D_157
      | k1_funct_1(C_160,E_159) != k1_funct_1(C_160,D_157)
      | ~ r2_hidden(E_159,A_158)
      | ~ r2_hidden(D_157,A_158)
      | ~ v2_funct_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156)))
      | ~ v1_funct_2(C_160,A_158,B_156)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_325,plain,(
    ! [D_44,E_159,B_156,A_158,B_29,A_6] :
      ( k1_xboole_0 = B_156
      | E_159 = '#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44)
      | k1_funct_1(A_6,E_159) != D_44
      | ~ r2_hidden(E_159,A_158)
      | ~ r2_hidden('#skF_4'(A_6,B_29,k9_relat_1(A_6,B_29),D_44),A_158)
      | ~ v2_funct_1(A_6)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(k2_zfmisc_1(A_158,B_156)))
      | ~ v1_funct_2(A_6,A_158,B_156)
      | ~ v1_funct_1(A_6)
      | ~ r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_317])).

tff(c_39342,plain,(
    ! [E_789,A_793,B_792,A_791,B_790] :
      ( k1_xboole_0 = B_790
      | '#skF_4'(A_793,B_792,k9_relat_1(A_793,B_792),k1_funct_1(A_793,E_789)) = E_789
      | ~ r2_hidden(E_789,A_791)
      | ~ r2_hidden('#skF_4'(A_793,B_792,k9_relat_1(A_793,B_792),k1_funct_1(A_793,E_789)),A_791)
      | ~ v2_funct_1(A_793)
      | ~ m1_subset_1(A_793,k1_zfmisc_1(k2_zfmisc_1(A_791,B_790)))
      | ~ v1_funct_2(A_793,A_791,B_790)
      | ~ v1_funct_1(A_793)
      | ~ r2_hidden(k1_funct_1(A_793,E_789),k9_relat_1(A_793,B_792))
      | ~ v1_funct_1(A_793)
      | ~ v1_relat_1(A_793) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_325])).

tff(c_39396,plain,(
    ! [B_790,E_789] :
      ( k1_xboole_0 = B_790
      | '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',E_789)) = E_789
      | ~ r2_hidden(E_789,'#skF_7')
      | ~ v2_funct_1('#skF_10')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_790)))
      | ~ v1_funct_2('#skF_10','#skF_7',B_790)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(k1_funct_1('#skF_10',E_789),k9_relat_1('#skF_10','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_26810,c_39342])).

tff(c_39582,plain,(
    ! [B_790,E_789] :
      ( k1_xboole_0 = B_790
      | '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',E_789)) = E_789
      | ~ r2_hidden(E_789,'#skF_7')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_790)))
      | ~ v1_funct_2('#skF_10','#skF_7',B_790)
      | ~ r2_hidden(k1_funct_1('#skF_10',E_789),k9_relat_1('#skF_10','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_74,c_68,c_39396])).

tff(c_41085,plain,(
    ! [E_805] :
      ( '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',E_805)) = E_805
      | ~ r2_hidden(E_805,'#skF_7')
      | ~ r2_hidden(k1_funct_1('#skF_10',E_805),k9_relat_1('#skF_10','#skF_7')) ) ),
    inference(splitLeft,[status(thm)],[c_39582])).

tff(c_41220,plain,(
    ! [C_806] :
      ( '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10',C_806)) = C_806
      | ~ r2_hidden(C_806,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_247,c_41085])).

tff(c_62,plain,(
    k1_funct_1(k2_funct_1('#skF_10'),k1_funct_1('#skF_10','#skF_9')) != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_441,plain,
    ( '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10','#skF_9')) != '#skF_9'
    | ~ r2_hidden('#skF_9','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_62])).

tff(c_459,plain,(
    '#skF_4'('#skF_10','#skF_7',k9_relat_1('#skF_10','#skF_7'),k1_funct_1('#skF_10','#skF_9')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_441])).

tff(c_41443,plain,(
    ~ r2_hidden('#skF_9','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_41220,c_459])).

tff(c_41607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_41443])).

tff(c_41609,plain,(
    ! [B_807] :
      ( k1_xboole_0 = B_807
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_807)))
      | ~ v1_funct_2('#skF_10','#skF_7',B_807) ) ),
    inference(splitRight,[status(thm)],[c_39582])).

tff(c_41612,plain,
    ( k1_xboole_0 = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_41609])).

tff(c_41615,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_41612])).

tff(c_41617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_41615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.29/9.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.29/9.07  
% 17.29/9.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.29/9.07  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_10 > #skF_5 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 17.29/9.07  
% 17.29/9.07  %Foreground sorts:
% 17.29/9.07  
% 17.29/9.07  
% 17.29/9.07  %Background operators:
% 17.29/9.07  
% 17.29/9.07  
% 17.29/9.07  %Foreground operators:
% 17.29/9.07  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 17.29/9.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.29/9.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 17.29/9.07  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 17.29/9.07  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 17.29/9.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.29/9.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.29/9.07  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 17.29/9.07  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 17.29/9.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.29/9.07  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 17.29/9.07  tff('#skF_7', type, '#skF_7': $i).
% 17.29/9.07  tff('#skF_10', type, '#skF_10': $i).
% 17.29/9.07  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 17.29/9.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 17.29/9.07  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 17.29/9.07  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 17.29/9.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.29/9.07  tff('#skF_9', type, '#skF_9': $i).
% 17.29/9.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 17.29/9.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.29/9.07  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 17.29/9.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 17.29/9.07  tff('#skF_8', type, '#skF_8': $i).
% 17.29/9.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.29/9.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 17.29/9.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 17.29/9.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.29/9.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.29/9.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 17.29/9.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.29/9.07  
% 17.29/9.09  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 17.29/9.09  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 17.29/9.09  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 17.29/9.09  tff(f_106, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 17.29/9.09  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 17.29/9.09  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 17.29/9.09  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 17.29/9.09  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 17.29/9.09  tff(f_94, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (v2_funct_1(C) <=> (![D, E]: (((r2_hidden(D, A) & r2_hidden(E, A)) & (k1_funct_1(C, D) = k1_funct_1(C, E))) => (D = E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_2)).
% 17.29/9.09  tff(c_64, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.29/9.09  tff(c_72, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.29/9.09  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.29/9.09  tff(c_66, plain, (r2_hidden('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.29/9.09  tff(c_74, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.29/9.09  tff(c_83, plain, (![A_74, B_75, C_76, D_77]: (k7_relset_1(A_74, B_75, C_76, D_77)=k9_relat_1(C_76, D_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 17.29/9.09  tff(c_86, plain, (![D_77]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_77)=k9_relat_1('#skF_10', D_77))), inference(resolution, [status(thm)], [c_70, c_83])).
% 17.29/9.09  tff(c_104, plain, (![A_82, B_83, C_84]: (k7_relset_1(A_82, B_83, C_84, A_82)=k2_relset_1(A_82, B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.29/9.09  tff(c_106, plain, (k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_7')=k2_relset_1('#skF_7', '#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_70, c_104])).
% 17.29/9.09  tff(c_108, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_10')=k9_relat_1('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_106])).
% 17.29/9.09  tff(c_229, plain, (![D_128, C_129, A_130, B_131]: (r2_hidden(k1_funct_1(D_128, C_129), k2_relset_1(A_130, B_131, D_128)) | k1_xboole_0=B_131 | ~r2_hidden(C_129, A_130) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_2(D_128, A_130, B_131) | ~v1_funct_1(D_128))), inference(cnfTransformation, [status(thm)], [f_106])).
% 17.29/9.09  tff(c_241, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_10', C_129), k9_relat_1('#skF_10', '#skF_7')) | k1_xboole_0='#skF_8' | ~r2_hidden(C_129, '#skF_7') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_229])).
% 17.29/9.09  tff(c_246, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_10', C_129), k9_relat_1('#skF_10', '#skF_7')) | k1_xboole_0='#skF_8' | ~r2_hidden(C_129, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_241])).
% 17.29/9.09  tff(c_247, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_10', C_129), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(C_129, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_64, c_246])).
% 17.29/9.09  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.29/9.09  tff(c_76, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 17.29/9.09  tff(c_79, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_70, c_76])).
% 17.29/9.09  tff(c_82, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_79])).
% 17.29/9.09  tff(c_68, plain, (v2_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.29/9.09  tff(c_12, plain, (![A_6, B_29, D_44]: (r2_hidden('#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44), k1_relat_1(A_6)) | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.29/9.09  tff(c_10, plain, (![A_6, B_29, D_44]: (r2_hidden('#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44), B_29) | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.29/9.09  tff(c_8, plain, (![A_6, B_29, D_44]: (k1_funct_1(A_6, '#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44))=D_44 | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.29/9.09  tff(c_32, plain, (![B_49, A_48]: (k1_funct_1(k2_funct_1(B_49), k1_funct_1(B_49, A_48))=A_48 | ~r2_hidden(A_48, k1_relat_1(B_49)) | ~v2_funct_1(B_49) | ~v1_funct_1(B_49) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 17.29/9.09  tff(c_155, plain, (![A_98, B_99, D_100]: (k1_funct_1(A_98, '#skF_4'(A_98, B_99, k9_relat_1(A_98, B_99), D_100))=D_100 | ~r2_hidden(D_100, k9_relat_1(A_98, B_99)) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.29/9.09  tff(c_365, plain, (![A_170, D_171, B_172]: (k1_funct_1(k2_funct_1(A_170), D_171)='#skF_4'(A_170, B_172, k9_relat_1(A_170, B_172), D_171) | ~r2_hidden('#skF_4'(A_170, B_172, k9_relat_1(A_170, B_172), D_171), k1_relat_1(A_170)) | ~v2_funct_1(A_170) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170) | ~r2_hidden(D_171, k9_relat_1(A_170, B_172)) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(superposition, [status(thm), theory('equality')], [c_155, c_32])).
% 17.29/9.09  tff(c_375, plain, (![A_173, D_174, B_175]: (k1_funct_1(k2_funct_1(A_173), D_174)='#skF_4'(A_173, B_175, k9_relat_1(A_173, B_175), D_174) | ~v2_funct_1(A_173) | ~r2_hidden(D_174, k9_relat_1(A_173, B_175)) | ~v1_funct_1(A_173) | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_12, c_365])).
% 17.29/9.09  tff(c_377, plain, (![C_129]: (k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_129))='#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', C_129)) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_129, '#skF_7'))), inference(resolution, [status(thm)], [c_247, c_375])).
% 17.29/9.09  tff(c_404, plain, (![C_176]: (k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_176))='#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', C_176)) | ~r2_hidden(C_176, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_68, c_377])).
% 17.29/9.09  tff(c_450, plain, (![B_29, D_44]: ('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', '#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44)))=k1_funct_1(k2_funct_1('#skF_10'), D_44) | ~r2_hidden('#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', B_29)) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_404])).
% 17.29/9.09  tff(c_17424, plain, (![B_538, D_539]: ('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', '#skF_4'('#skF_10', B_538, k9_relat_1('#skF_10', B_538), D_539)))=k1_funct_1(k2_funct_1('#skF_10'), D_539) | ~r2_hidden('#skF_4'('#skF_10', B_538, k9_relat_1('#skF_10', B_538), D_539), '#skF_7') | ~r2_hidden(D_539, k9_relat_1('#skF_10', B_538)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_450])).
% 17.29/9.09  tff(c_17551, plain, (![D_539, B_538]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), D_539), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_10', '#skF_4'('#skF_10', B_538, k9_relat_1('#skF_10', B_538), D_539)), k9_relat_1('#skF_10', '#skF_7')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden('#skF_4'('#skF_10', B_538, k9_relat_1('#skF_10', B_538), D_539), '#skF_7') | ~r2_hidden(D_539, k9_relat_1('#skF_10', B_538)))), inference(superposition, [status(thm), theory('equality')], [c_17424, c_10])).
% 17.29/9.09  tff(c_19527, plain, (![D_574, B_575]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), D_574), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_10', '#skF_4'('#skF_10', B_575, k9_relat_1('#skF_10', B_575), D_574)), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_10', B_575, k9_relat_1('#skF_10', B_575), D_574), '#skF_7') | ~r2_hidden(D_574, k9_relat_1('#skF_10', B_575)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_17551])).
% 17.29/9.09  tff(c_19647, plain, (![D_576, B_577]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), D_576), '#skF_7') | ~r2_hidden(D_576, k9_relat_1('#skF_10', B_577)) | ~r2_hidden('#skF_4'('#skF_10', B_577, k9_relat_1('#skF_10', B_577), D_576), '#skF_7'))), inference(resolution, [status(thm)], [c_247, c_19527])).
% 17.29/9.09  tff(c_19696, plain, (![D_44]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', '#skF_7')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_10, c_19647])).
% 17.29/9.09  tff(c_19711, plain, (![D_578]: (r2_hidden(k1_funct_1(k2_funct_1('#skF_10'), D_578), '#skF_7') | ~r2_hidden(D_578, k9_relat_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_19696])).
% 17.29/9.09  tff(c_19785, plain, (![A_48]: (r2_hidden(A_48, '#skF_7') | ~r2_hidden(k1_funct_1('#skF_10', A_48), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(A_48, k1_relat_1('#skF_10')) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_19711])).
% 17.29/9.09  tff(c_19806, plain, (![A_579]: (r2_hidden(A_579, '#skF_7') | ~r2_hidden(k1_funct_1('#skF_10', A_579), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(A_579, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_68, c_19785])).
% 17.29/9.09  tff(c_19865, plain, (![B_29, D_44]: (r2_hidden('#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44), k1_relat_1('#skF_10')) | ~r2_hidden(D_44, k9_relat_1('#skF_10', B_29)) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_19806])).
% 17.29/9.09  tff(c_21097, plain, (![B_608, D_609]: (r2_hidden('#skF_4'('#skF_10', B_608, k9_relat_1('#skF_10', B_608), D_609), '#skF_7') | ~r2_hidden(D_609, k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_10', B_608, k9_relat_1('#skF_10', B_608), D_609), k1_relat_1('#skF_10')) | ~r2_hidden(D_609, k9_relat_1('#skF_10', B_608)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_19865])).
% 17.29/9.09  tff(c_21203, plain, (![B_29, D_44]: (r2_hidden('#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(D_44, k9_relat_1('#skF_10', B_29)) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_12, c_21097])).
% 17.29/9.09  tff(c_21237, plain, (![B_610, D_611]: (r2_hidden('#skF_4'('#skF_10', B_610, k9_relat_1('#skF_10', B_610), D_611), '#skF_7') | ~r2_hidden(D_611, k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(D_611, k9_relat_1('#skF_10', B_610)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_21203])).
% 17.29/9.09  tff(c_397, plain, (![C_129]: (k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_129))='#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', C_129)) | ~r2_hidden(C_129, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_68, c_377])).
% 17.29/9.09  tff(c_6, plain, (![A_6, E_47, B_29]: (r2_hidden(k1_funct_1(A_6, E_47), k9_relat_1(A_6, B_29)) | ~r2_hidden(E_47, B_29) | ~r2_hidden(E_47, k1_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.29/9.09  tff(c_614, plain, (![D_181, A_182, B_183, B_184]: (r2_hidden(D_181, k9_relat_1(A_182, B_183)) | ~r2_hidden('#skF_4'(A_182, B_184, k9_relat_1(A_182, B_184), D_181), B_183) | ~r2_hidden('#skF_4'(A_182, B_184, k9_relat_1(A_182, B_184), D_181), k1_relat_1(A_182)) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182) | ~r2_hidden(D_181, k9_relat_1(A_182, B_184)) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_155, c_6])).
% 17.29/9.09  tff(c_627, plain, (![D_185, A_186, B_187]: (r2_hidden(D_185, k9_relat_1(A_186, k1_relat_1(A_186))) | ~r2_hidden('#skF_4'(A_186, B_187, k9_relat_1(A_186, B_187), D_185), k1_relat_1(A_186)) | ~r2_hidden(D_185, k9_relat_1(A_186, B_187)) | ~v1_funct_1(A_186) | ~v1_relat_1(A_186))), inference(resolution, [status(thm)], [c_12, c_614])).
% 17.29/9.09  tff(c_645, plain, (![D_188, A_189, B_190]: (r2_hidden(D_188, k9_relat_1(A_189, k1_relat_1(A_189))) | ~r2_hidden(D_188, k9_relat_1(A_189, B_190)) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_12, c_627])).
% 17.29/9.09  tff(c_647, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_10', C_129), k9_relat_1('#skF_10', k1_relat_1('#skF_10'))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_129, '#skF_7'))), inference(resolution, [status(thm)], [c_247, c_645])).
% 17.29/9.09  tff(c_667, plain, (![C_129]: (r2_hidden(k1_funct_1('#skF_10', C_129), k9_relat_1('#skF_10', k1_relat_1('#skF_10'))) | ~r2_hidden(C_129, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_647])).
% 17.29/9.09  tff(c_674, plain, (![C_191]: (r2_hidden(k1_funct_1('#skF_10', C_191), k9_relat_1('#skF_10', k1_relat_1('#skF_10'))) | ~r2_hidden(C_191, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_647])).
% 17.29/9.09  tff(c_373, plain, (![A_6, D_44, B_29]: (k1_funct_1(k2_funct_1(A_6), D_44)='#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44) | ~v2_funct_1(A_6) | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_12, c_365])).
% 17.29/9.09  tff(c_678, plain, (![C_191]: ('#skF_4'('#skF_10', k1_relat_1('#skF_10'), k9_relat_1('#skF_10', k1_relat_1('#skF_10')), k1_funct_1('#skF_10', C_191))=k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_191)) | ~v2_funct_1('#skF_10') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_191, '#skF_7'))), inference(resolution, [status(thm)], [c_674, c_373])).
% 17.29/9.09  tff(c_745, plain, (![C_196]: ('#skF_4'('#skF_10', k1_relat_1('#skF_10'), k9_relat_1('#skF_10', k1_relat_1('#skF_10')), k1_funct_1('#skF_10', C_196))=k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_196)) | ~r2_hidden(C_196, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_68, c_678])).
% 17.29/9.09  tff(c_759, plain, (![C_196]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_196)))=k1_funct_1('#skF_10', C_196) | ~r2_hidden(k1_funct_1('#skF_10', C_196), k9_relat_1('#skF_10', k1_relat_1('#skF_10'))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_196, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_745, c_8])).
% 17.29/9.09  tff(c_1296, plain, (![C_216]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_216)))=k1_funct_1('#skF_10', C_216) | ~r2_hidden(k1_funct_1('#skF_10', C_216), k9_relat_1('#skF_10', k1_relat_1('#skF_10'))) | ~r2_hidden(C_216, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_759])).
% 17.29/9.09  tff(c_1344, plain, (![C_217]: (k1_funct_1('#skF_10', k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', C_217)))=k1_funct_1('#skF_10', C_217) | ~r2_hidden(C_217, '#skF_7'))), inference(resolution, [status(thm)], [c_667, c_1296])).
% 17.29/9.09  tff(c_1486, plain, (![C_218]: (k1_funct_1('#skF_10', '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', C_218)))=k1_funct_1('#skF_10', C_218) | ~r2_hidden(C_218, '#skF_7') | ~r2_hidden(C_218, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_397, c_1344])).
% 17.29/9.09  tff(c_1577, plain, (![B_29, D_44]: (k1_funct_1('#skF_10', '#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44))=k1_funct_1('#skF_10', '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_44)) | ~r2_hidden('#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44), '#skF_7') | ~r2_hidden('#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', B_29)) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1486])).
% 17.29/9.09  tff(c_1621, plain, (![B_29, D_44]: (k1_funct_1('#skF_10', '#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44))=k1_funct_1('#skF_10', '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_44)) | ~r2_hidden('#skF_4'('#skF_10', B_29, k9_relat_1('#skF_10', B_29), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_1577])).
% 17.29/9.09  tff(c_24932, plain, (![B_642, D_643]: (k1_funct_1('#skF_10', '#skF_4'('#skF_10', B_642, k9_relat_1('#skF_10', B_642), D_643))=k1_funct_1('#skF_10', '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_643)) | ~r2_hidden(D_643, k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(D_643, k9_relat_1('#skF_10', B_642)))), inference(resolution, [status(thm)], [c_21237, c_1621])).
% 17.29/9.09  tff(c_26503, plain, (![D_652, B_653]: (r2_hidden(k1_funct_1('#skF_10', '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_652)), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden('#skF_4'('#skF_10', B_653, k9_relat_1('#skF_10', B_653), D_652), '#skF_7') | ~r2_hidden(D_652, k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(D_652, k9_relat_1('#skF_10', B_653)))), inference(superposition, [status(thm), theory('equality')], [c_24932, c_247])).
% 17.29/9.09  tff(c_26560, plain, (![D_44]: (r2_hidden(k1_funct_1('#skF_10', '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_44)), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(D_44, k9_relat_1('#skF_10', '#skF_7')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_10, c_26503])).
% 17.29/9.09  tff(c_26578, plain, (![D_654]: (r2_hidden(k1_funct_1('#skF_10', '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_654)), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(D_654, k9_relat_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_26560])).
% 17.29/9.09  tff(c_19805, plain, (![A_48]: (r2_hidden(A_48, '#skF_7') | ~r2_hidden(k1_funct_1('#skF_10', A_48), k9_relat_1('#skF_10', '#skF_7')) | ~r2_hidden(A_48, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_68, c_19785])).
% 17.29/9.09  tff(c_26703, plain, (![D_655]: (r2_hidden('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_655), '#skF_7') | ~r2_hidden('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_655), k1_relat_1('#skF_10')) | ~r2_hidden(D_655, k9_relat_1('#skF_10', '#skF_7')))), inference(resolution, [status(thm)], [c_26578, c_19805])).
% 17.29/9.09  tff(c_26791, plain, (![D_44]: (r2_hidden('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', '#skF_7')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_12, c_26703])).
% 17.29/9.09  tff(c_26810, plain, (![D_44]: (r2_hidden('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), D_44), '#skF_7') | ~r2_hidden(D_44, k9_relat_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_26791])).
% 17.29/9.09  tff(c_317, plain, (![C_160, D_157, E_159, B_156, A_158]: (k1_xboole_0=B_156 | E_159=D_157 | k1_funct_1(C_160, E_159)!=k1_funct_1(C_160, D_157) | ~r2_hidden(E_159, A_158) | ~r2_hidden(D_157, A_158) | ~v2_funct_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))) | ~v1_funct_2(C_160, A_158, B_156) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_94])).
% 17.29/9.09  tff(c_325, plain, (![D_44, E_159, B_156, A_158, B_29, A_6]: (k1_xboole_0=B_156 | E_159='#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44) | k1_funct_1(A_6, E_159)!=D_44 | ~r2_hidden(E_159, A_158) | ~r2_hidden('#skF_4'(A_6, B_29, k9_relat_1(A_6, B_29), D_44), A_158) | ~v2_funct_1(A_6) | ~m1_subset_1(A_6, k1_zfmisc_1(k2_zfmisc_1(A_158, B_156))) | ~v1_funct_2(A_6, A_158, B_156) | ~v1_funct_1(A_6) | ~r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_317])).
% 17.29/9.09  tff(c_39342, plain, (![E_789, A_793, B_792, A_791, B_790]: (k1_xboole_0=B_790 | '#skF_4'(A_793, B_792, k9_relat_1(A_793, B_792), k1_funct_1(A_793, E_789))=E_789 | ~r2_hidden(E_789, A_791) | ~r2_hidden('#skF_4'(A_793, B_792, k9_relat_1(A_793, B_792), k1_funct_1(A_793, E_789)), A_791) | ~v2_funct_1(A_793) | ~m1_subset_1(A_793, k1_zfmisc_1(k2_zfmisc_1(A_791, B_790))) | ~v1_funct_2(A_793, A_791, B_790) | ~v1_funct_1(A_793) | ~r2_hidden(k1_funct_1(A_793, E_789), k9_relat_1(A_793, B_792)) | ~v1_funct_1(A_793) | ~v1_relat_1(A_793))), inference(reflexivity, [status(thm), theory('equality')], [c_325])).
% 17.29/9.09  tff(c_39396, plain, (![B_790, E_789]: (k1_xboole_0=B_790 | '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', E_789))=E_789 | ~r2_hidden(E_789, '#skF_7') | ~v2_funct_1('#skF_10') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_790))) | ~v1_funct_2('#skF_10', '#skF_7', B_790) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(k1_funct_1('#skF_10', E_789), k9_relat_1('#skF_10', '#skF_7')))), inference(resolution, [status(thm)], [c_26810, c_39342])).
% 17.29/9.09  tff(c_39582, plain, (![B_790, E_789]: (k1_xboole_0=B_790 | '#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', E_789))=E_789 | ~r2_hidden(E_789, '#skF_7') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_790))) | ~v1_funct_2('#skF_10', '#skF_7', B_790) | ~r2_hidden(k1_funct_1('#skF_10', E_789), k9_relat_1('#skF_10', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_74, c_68, c_39396])).
% 17.29/9.09  tff(c_41085, plain, (![E_805]: ('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', E_805))=E_805 | ~r2_hidden(E_805, '#skF_7') | ~r2_hidden(k1_funct_1('#skF_10', E_805), k9_relat_1('#skF_10', '#skF_7')))), inference(splitLeft, [status(thm)], [c_39582])).
% 17.29/9.09  tff(c_41220, plain, (![C_806]: ('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', C_806))=C_806 | ~r2_hidden(C_806, '#skF_7'))), inference(resolution, [status(thm)], [c_247, c_41085])).
% 17.29/9.09  tff(c_62, plain, (k1_funct_1(k2_funct_1('#skF_10'), k1_funct_1('#skF_10', '#skF_9'))!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_121])).
% 17.29/9.09  tff(c_441, plain, ('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', '#skF_9'))!='#skF_9' | ~r2_hidden('#skF_9', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_404, c_62])).
% 17.29/9.09  tff(c_459, plain, ('#skF_4'('#skF_10', '#skF_7', k9_relat_1('#skF_10', '#skF_7'), k1_funct_1('#skF_10', '#skF_9'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_441])).
% 17.29/9.09  tff(c_41443, plain, (~r2_hidden('#skF_9', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_41220, c_459])).
% 17.29/9.09  tff(c_41607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_41443])).
% 17.29/9.09  tff(c_41609, plain, (![B_807]: (k1_xboole_0=B_807 | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_807))) | ~v1_funct_2('#skF_10', '#skF_7', B_807))), inference(splitRight, [status(thm)], [c_39582])).
% 17.29/9.09  tff(c_41612, plain, (k1_xboole_0='#skF_8' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_41609])).
% 17.29/9.09  tff(c_41615, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_41612])).
% 17.29/9.09  tff(c_41617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_41615])).
% 17.29/9.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.29/9.09  
% 17.29/9.09  Inference rules
% 17.29/9.09  ----------------------
% 17.29/9.09  #Ref     : 17
% 17.29/9.09  #Sup     : 11386
% 17.29/9.09  #Fact    : 0
% 17.29/9.09  #Define  : 0
% 17.29/9.09  #Split   : 3
% 17.29/9.09  #Chain   : 0
% 17.29/9.09  #Close   : 0
% 17.29/9.09  
% 17.29/9.09  Ordering : KBO
% 17.29/9.09  
% 17.29/9.09  Simplification rules
% 17.29/9.09  ----------------------
% 17.29/9.09  #Subsume      : 4492
% 17.29/9.09  #Demod        : 7417
% 17.29/9.09  #Tautology    : 1207
% 17.29/9.09  #SimpNegUnit  : 21
% 17.29/9.09  #BackRed      : 0
% 17.29/9.09  
% 17.29/9.09  #Partial instantiations: 0
% 17.29/9.09  #Strategies tried      : 1
% 17.29/9.09  
% 17.29/9.09  Timing (in seconds)
% 17.29/9.09  ----------------------
% 17.29/9.09  Preprocessing        : 0.36
% 17.29/9.09  Parsing              : 0.18
% 17.29/9.09  CNF conversion       : 0.03
% 17.29/9.09  Main loop            : 7.96
% 17.29/9.09  Inferencing          : 1.78
% 17.29/9.09  Reduction            : 1.99
% 17.29/9.10  Demodulation         : 1.36
% 17.29/9.10  BG Simplification    : 0.24
% 17.29/9.10  Subsumption          : 3.56
% 17.29/9.10  Abstraction          : 0.46
% 17.29/9.10  MUC search           : 0.00
% 17.29/9.10  Cooper               : 0.00
% 17.29/9.10  Total                : 8.36
% 17.29/9.10  Index Insertion      : 0.00
% 17.29/9.10  Index Deletion       : 0.00
% 17.29/9.10  Index Matching       : 0.00
% 17.29/9.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
