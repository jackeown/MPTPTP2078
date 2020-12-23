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
% DateTime   : Thu Dec  3 10:18:09 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  119 (1185 expanded)
%              Number of leaves         :   36 ( 428 expanded)
%              Depth                    :   24
%              Number of atoms          :  225 (4079 expanded)
%              Number of equality atoms :   48 ( 874 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_172,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_187,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_172])).

tff(c_56,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_188,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_56])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_62,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_112])).

tff(c_122,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_118])).

tff(c_152,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_167,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_152])).

tff(c_3030,plain,(
    ! [B_337,A_338,C_339] :
      ( k1_xboole_0 = B_337
      | k1_relset_1(A_338,B_337,C_339) = A_338
      | ~ v1_funct_2(C_339,A_338,B_337)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3044,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_3030])).

tff(c_3056,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_167,c_3044])).

tff(c_3058,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3056])).

tff(c_50,plain,(
    ! [C_32,B_31] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_32),B_31,C_32),k1_relat_1(C_32))
      | v1_funct_2(C_32,k1_relat_1(C_32),B_31)
      | ~ v1_funct_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3067,plain,(
    ! [B_31] :
      ( r2_hidden('#skF_1'('#skF_3',B_31,'#skF_5'),k1_relat_1('#skF_5'))
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_31)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3058,c_50])).

tff(c_3202,plain,(
    ! [B_347] :
      ( r2_hidden('#skF_1'('#skF_3',B_347,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_64,c_3058,c_3058,c_3067])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3206,plain,(
    ! [B_347] :
      ( m1_subset_1('#skF_1'('#skF_3',B_347,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_347) ) ),
    inference(resolution,[status(thm)],[c_3202,c_8])).

tff(c_3837,plain,(
    ! [A_390,B_391,C_392,D_393] :
      ( k3_funct_2(A_390,B_391,C_392,D_393) = k1_funct_1(C_392,D_393)
      | ~ m1_subset_1(D_393,A_390)
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1(A_390,B_391)))
      | ~ v1_funct_2(C_392,A_390,B_391)
      | ~ v1_funct_1(C_392)
      | v1_xboole_0(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3847,plain,(
    ! [B_391,C_392,B_347] :
      ( k3_funct_2('#skF_3',B_391,C_392,'#skF_1'('#skF_3',B_347,'#skF_5')) = k1_funct_1(C_392,'#skF_1'('#skF_3',B_347,'#skF_5'))
      | ~ m1_subset_1(C_392,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_391)))
      | ~ v1_funct_2(C_392,'#skF_3',B_391)
      | ~ v1_funct_1(C_392)
      | v1_xboole_0('#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_347) ) ),
    inference(resolution,[status(thm)],[c_3206,c_3837])).

tff(c_4039,plain,(
    ! [B_408,C_409,B_410] :
      ( k3_funct_2('#skF_3',B_408,C_409,'#skF_1'('#skF_3',B_410,'#skF_5')) = k1_funct_1(C_409,'#skF_1'('#skF_3',B_410,'#skF_5'))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_408)))
      | ~ v1_funct_2(C_409,'#skF_3',B_408)
      | ~ v1_funct_1(C_409)
      | v1_funct_2('#skF_5','#skF_3',B_410) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3847])).

tff(c_4051,plain,(
    ! [B_410] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_410,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_410,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_funct_2('#skF_5','#skF_3',B_410) ) ),
    inference(resolution,[status(thm)],[c_60,c_4039])).

tff(c_4800,plain,(
    ! [B_468] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_468,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_468,'#skF_5'))
      | v1_funct_2('#skF_5','#skF_3',B_468) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_4051])).

tff(c_58,plain,(
    ! [E_45] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_45),'#skF_2')
      | ~ m1_subset_1(E_45,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_4837,plain,(
    ! [B_472] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_472,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_472,'#skF_5'),'#skF_3')
      | v1_funct_2('#skF_5','#skF_3',B_472) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4800,c_58])).

tff(c_3286,plain,(
    ! [C_354,B_355] :
      ( ~ r2_hidden(k1_funct_1(C_354,'#skF_1'(k1_relat_1(C_354),B_355,C_354)),B_355)
      | v1_funct_2(C_354,k1_relat_1(C_354),B_355)
      | ~ v1_funct_1(C_354)
      | ~ v1_relat_1(C_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3289,plain,(
    ! [B_355] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_355,'#skF_5')),B_355)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_355)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3058,c_3286])).

tff(c_3291,plain,(
    ! [B_355] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_355,'#skF_5')),B_355)
      | v1_funct_2('#skF_5','#skF_3',B_355) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_64,c_3058,c_3289])).

tff(c_4850,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4837,c_3291])).

tff(c_4852,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4850])).

tff(c_3487,plain,(
    ! [C_370,B_371] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_370),B_371,C_370),k1_relat_1(C_370))
      | m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_370),B_371)))
      | ~ v1_funct_1(C_370)
      | ~ v1_relat_1(C_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3493,plain,(
    ! [B_371] :
      ( r2_hidden('#skF_1'('#skF_3',B_371,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_371)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3058,c_3487])).

tff(c_3502,plain,(
    ! [B_372] :
      ( r2_hidden('#skF_1'('#skF_3',B_372,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_372))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_64,c_3058,c_3058,c_3493])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_3758,plain,(
    ! [B_386] :
      ( k2_relset_1('#skF_3',B_386,'#skF_5') = k2_relat_1('#skF_5')
      | r2_hidden('#skF_1'('#skF_3',B_386,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3502,c_22])).

tff(c_3762,plain,(
    ! [B_386] :
      ( m1_subset_1('#skF_1'('#skF_3',B_386,'#skF_5'),'#skF_3')
      | k2_relset_1('#skF_3',B_386,'#skF_5') = k2_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3758,c_8])).

tff(c_4866,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3762,c_4852])).

tff(c_235,plain,(
    ! [A_93,B_94,C_95] :
      ( m1_subset_1(k2_relset_1(A_93,B_94,C_95),k1_zfmisc_1(B_94))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_276,plain,(
    ! [A_93,B_94,C_95] :
      ( r1_tarski(k2_relset_1(A_93,B_94,C_95),B_94)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(resolution,[status(thm)],[c_235,c_10])).

tff(c_3763,plain,(
    ! [B_387] :
      ( r1_tarski(k2_relset_1('#skF_3',B_387,'#skF_5'),B_387)
      | r2_hidden('#skF_1'('#skF_3',B_387,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3502,c_276])).

tff(c_3791,plain,(
    ! [B_387] :
      ( m1_subset_1('#skF_1'('#skF_3',B_387,'#skF_5'),'#skF_3')
      | r1_tarski(k2_relset_1('#skF_3',B_387,'#skF_5'),B_387) ) ),
    inference(resolution,[status(thm)],[c_3763,c_8])).

tff(c_4914,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4866,c_3791])).

tff(c_4928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_4852,c_4914])).

tff(c_4930,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_4850])).

tff(c_36,plain,(
    ! [A_24,B_25,C_26,D_27] :
      ( k3_funct_2(A_24,B_25,C_26,D_27) = k1_funct_1(C_26,D_27)
      | ~ m1_subset_1(D_27,A_24)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25)))
      | ~ v1_funct_2(C_26,A_24,B_25)
      | ~ v1_funct_1(C_26)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4942,plain,(
    ! [B_25,C_26] :
      ( k3_funct_2('#skF_3',B_25,C_26,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_26,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_25)))
      | ~ v1_funct_2(C_26,'#skF_3',B_25)
      | ~ v1_funct_1(C_26)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4930,c_36])).

tff(c_5049,plain,(
    ! [B_485,C_486] :
      ( k3_funct_2('#skF_3',B_485,C_486,'#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1(C_486,'#skF_1'('#skF_3','#skF_2','#skF_5'))
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_485)))
      | ~ v1_funct_2(C_486,'#skF_3',B_485)
      | ~ v1_funct_1(C_486) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4942])).

tff(c_5073,plain,
    ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5'))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_5049])).

tff(c_5092,plain,(
    k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_5073])).

tff(c_5352,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5092,c_58])).

tff(c_5363,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3','#skF_2','#skF_5')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4930,c_5352])).

tff(c_3724,plain,(
    ! [C_381,B_382] :
      ( ~ r2_hidden(k1_funct_1(C_381,'#skF_1'(k1_relat_1(C_381),B_382,C_381)),B_382)
      | m1_subset_1(C_381,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_381),B_382)))
      | ~ v1_funct_1(C_381)
      | ~ v1_relat_1(C_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3727,plain,(
    ! [B_382] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_382,'#skF_5')),B_382)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_382)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3058,c_3724])).

tff(c_3729,plain,(
    ! [B_382] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_382,'#skF_5')),B_382)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_382))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_64,c_3058,c_3727])).

tff(c_5379,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_5363,c_3729])).

tff(c_5449,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5379,c_22])).

tff(c_5448,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5379,c_276])).

tff(c_5495,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5449,c_5448])).

tff(c_5497,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_5495])).

tff(c_5498,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3056])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5554,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5498,c_5498,c_4])).

tff(c_103,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_103])).

tff(c_5563,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5554,c_111])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5556,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_4',B_2) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5498,c_5498,c_6])).

tff(c_5613,plain,(
    ! [B_508] : k2_zfmisc_1('#skF_4',B_508) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5498,c_5498,c_6])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_186,plain,(
    ! [A_67,B_68,A_5] :
      ( k2_relset_1(A_67,B_68,A_5) = k2_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_12,c_172])).

tff(c_5715,plain,(
    ! [B_521,A_522] :
      ( k2_relset_1('#skF_4',B_521,A_522) = k2_relat_1(A_522)
      | ~ r1_tarski(A_522,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5613,c_186])).

tff(c_5727,plain,(
    ! [B_523] : k2_relset_1('#skF_4',B_523,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_5563,c_5715])).

tff(c_2755,plain,(
    ! [A_291,B_292,C_293] :
      ( r1_tarski(k2_relset_1(A_291,B_292,C_293),B_292)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(resolution,[status(thm)],[c_235,c_10])).

tff(c_2769,plain,(
    ! [A_291,B_292,A_5] :
      ( r1_tarski(k2_relset_1(A_291,B_292,A_5),B_292)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_291,B_292)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2755])).

tff(c_5736,plain,(
    ! [B_523] :
      ( r1_tarski(k2_relat_1('#skF_5'),B_523)
      | ~ r1_tarski('#skF_5',k2_zfmisc_1('#skF_4',B_523)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5727,c_2769])).

tff(c_5746,plain,(
    ! [B_523] : r1_tarski(k2_relat_1('#skF_5'),B_523) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5563,c_5556,c_5736])).

tff(c_5772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5746,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.63/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.36  
% 6.63/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.36  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.63/2.36  
% 6.63/2.36  %Foreground sorts:
% 6.63/2.36  
% 6.63/2.36  
% 6.63/2.36  %Background operators:
% 6.63/2.36  
% 6.63/2.36  
% 6.63/2.36  %Foreground operators:
% 6.63/2.36  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.63/2.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.63/2.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.63/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.63/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.63/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.63/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.63/2.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.63/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.63/2.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.63/2.36  tff('#skF_2', type, '#skF_2': $i).
% 6.63/2.36  tff('#skF_3', type, '#skF_3': $i).
% 6.63/2.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.63/2.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.63/2.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.63/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.63/2.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.63/2.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.63/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.63/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.63/2.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.63/2.37  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 6.63/2.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.63/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.63/2.37  
% 6.95/2.39  tff(f_142, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 6.95/2.39  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.95/2.39  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.95/2.39  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.95/2.39  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.95/2.39  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.95/2.39  tff(f_120, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 6.95/2.39  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.95/2.39  tff(f_91, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 6.95/2.39  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 6.95/2.39  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.95/2.39  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.95/2.39  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.95/2.39  tff(c_172, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.95/2.39  tff(c_187, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_172])).
% 6.95/2.39  tff(c_56, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.95/2.39  tff(c_188, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_56])).
% 6.95/2.39  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.95/2.39  tff(c_62, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.95/2.39  tff(c_68, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.95/2.39  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.95/2.39  tff(c_112, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.95/2.39  tff(c_118, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_112])).
% 6.95/2.39  tff(c_122, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_118])).
% 6.95/2.39  tff(c_152, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.95/2.39  tff(c_167, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_152])).
% 6.95/2.39  tff(c_3030, plain, (![B_337, A_338, C_339]: (k1_xboole_0=B_337 | k1_relset_1(A_338, B_337, C_339)=A_338 | ~v1_funct_2(C_339, A_338, B_337) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.95/2.39  tff(c_3044, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_3030])).
% 6.95/2.39  tff(c_3056, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_167, c_3044])).
% 6.95/2.39  tff(c_3058, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_3056])).
% 6.95/2.39  tff(c_50, plain, (![C_32, B_31]: (r2_hidden('#skF_1'(k1_relat_1(C_32), B_31, C_32), k1_relat_1(C_32)) | v1_funct_2(C_32, k1_relat_1(C_32), B_31) | ~v1_funct_1(C_32) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.95/2.39  tff(c_3067, plain, (![B_31]: (r2_hidden('#skF_1'('#skF_3', B_31, '#skF_5'), k1_relat_1('#skF_5')) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_31) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3058, c_50])).
% 6.95/2.39  tff(c_3202, plain, (![B_347]: (r2_hidden('#skF_1'('#skF_3', B_347, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_347))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_64, c_3058, c_3058, c_3067])).
% 6.95/2.39  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.95/2.39  tff(c_3206, plain, (![B_347]: (m1_subset_1('#skF_1'('#skF_3', B_347, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_347))), inference(resolution, [status(thm)], [c_3202, c_8])).
% 6.95/2.39  tff(c_3837, plain, (![A_390, B_391, C_392, D_393]: (k3_funct_2(A_390, B_391, C_392, D_393)=k1_funct_1(C_392, D_393) | ~m1_subset_1(D_393, A_390) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1(A_390, B_391))) | ~v1_funct_2(C_392, A_390, B_391) | ~v1_funct_1(C_392) | v1_xboole_0(A_390))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.95/2.39  tff(c_3847, plain, (![B_391, C_392, B_347]: (k3_funct_2('#skF_3', B_391, C_392, '#skF_1'('#skF_3', B_347, '#skF_5'))=k1_funct_1(C_392, '#skF_1'('#skF_3', B_347, '#skF_5')) | ~m1_subset_1(C_392, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_391))) | ~v1_funct_2(C_392, '#skF_3', B_391) | ~v1_funct_1(C_392) | v1_xboole_0('#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_347))), inference(resolution, [status(thm)], [c_3206, c_3837])).
% 6.95/2.39  tff(c_4039, plain, (![B_408, C_409, B_410]: (k3_funct_2('#skF_3', B_408, C_409, '#skF_1'('#skF_3', B_410, '#skF_5'))=k1_funct_1(C_409, '#skF_1'('#skF_3', B_410, '#skF_5')) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_408))) | ~v1_funct_2(C_409, '#skF_3', B_408) | ~v1_funct_1(C_409) | v1_funct_2('#skF_5', '#skF_3', B_410))), inference(negUnitSimplification, [status(thm)], [c_68, c_3847])).
% 6.95/2.39  tff(c_4051, plain, (![B_410]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_410, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_410, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_funct_2('#skF_5', '#skF_3', B_410))), inference(resolution, [status(thm)], [c_60, c_4039])).
% 6.95/2.39  tff(c_4800, plain, (![B_468]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_468, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_468, '#skF_5')) | v1_funct_2('#skF_5', '#skF_3', B_468))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_4051])).
% 6.95/2.39  tff(c_58, plain, (![E_45]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_45), '#skF_2') | ~m1_subset_1(E_45, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.95/2.39  tff(c_4837, plain, (![B_472]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_472, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_472, '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', B_472))), inference(superposition, [status(thm), theory('equality')], [c_4800, c_58])).
% 6.95/2.39  tff(c_3286, plain, (![C_354, B_355]: (~r2_hidden(k1_funct_1(C_354, '#skF_1'(k1_relat_1(C_354), B_355, C_354)), B_355) | v1_funct_2(C_354, k1_relat_1(C_354), B_355) | ~v1_funct_1(C_354) | ~v1_relat_1(C_354))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.95/2.39  tff(c_3289, plain, (![B_355]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_355, '#skF_5')), B_355) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_355) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3058, c_3286])).
% 6.95/2.39  tff(c_3291, plain, (![B_355]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_355, '#skF_5')), B_355) | v1_funct_2('#skF_5', '#skF_3', B_355))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_64, c_3058, c_3289])).
% 6.95/2.39  tff(c_4850, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4837, c_3291])).
% 6.95/2.39  tff(c_4852, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_4850])).
% 6.95/2.39  tff(c_3487, plain, (![C_370, B_371]: (r2_hidden('#skF_1'(k1_relat_1(C_370), B_371, C_370), k1_relat_1(C_370)) | m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_370), B_371))) | ~v1_funct_1(C_370) | ~v1_relat_1(C_370))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.95/2.39  tff(c_3493, plain, (![B_371]: (r2_hidden('#skF_1'('#skF_3', B_371, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_371))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3058, c_3487])).
% 6.95/2.39  tff(c_3502, plain, (![B_372]: (r2_hidden('#skF_1'('#skF_3', B_372, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_372))))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_64, c_3058, c_3058, c_3493])).
% 6.95/2.39  tff(c_22, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.95/2.39  tff(c_3758, plain, (![B_386]: (k2_relset_1('#skF_3', B_386, '#skF_5')=k2_relat_1('#skF_5') | r2_hidden('#skF_1'('#skF_3', B_386, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_3502, c_22])).
% 6.95/2.39  tff(c_3762, plain, (![B_386]: (m1_subset_1('#skF_1'('#skF_3', B_386, '#skF_5'), '#skF_3') | k2_relset_1('#skF_3', B_386, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_3758, c_8])).
% 6.95/2.39  tff(c_4866, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_3762, c_4852])).
% 6.95/2.39  tff(c_235, plain, (![A_93, B_94, C_95]: (m1_subset_1(k2_relset_1(A_93, B_94, C_95), k1_zfmisc_1(B_94)) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.95/2.39  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.95/2.39  tff(c_276, plain, (![A_93, B_94, C_95]: (r1_tarski(k2_relset_1(A_93, B_94, C_95), B_94) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(resolution, [status(thm)], [c_235, c_10])).
% 6.95/2.39  tff(c_3763, plain, (![B_387]: (r1_tarski(k2_relset_1('#skF_3', B_387, '#skF_5'), B_387) | r2_hidden('#skF_1'('#skF_3', B_387, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_3502, c_276])).
% 6.95/2.39  tff(c_3791, plain, (![B_387]: (m1_subset_1('#skF_1'('#skF_3', B_387, '#skF_5'), '#skF_3') | r1_tarski(k2_relset_1('#skF_3', B_387, '#skF_5'), B_387))), inference(resolution, [status(thm)], [c_3763, c_8])).
% 6.95/2.39  tff(c_4914, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4866, c_3791])).
% 6.95/2.39  tff(c_4928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_4852, c_4914])).
% 6.95/2.39  tff(c_4930, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_4850])).
% 6.95/2.39  tff(c_36, plain, (![A_24, B_25, C_26, D_27]: (k3_funct_2(A_24, B_25, C_26, D_27)=k1_funct_1(C_26, D_27) | ~m1_subset_1(D_27, A_24) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))) | ~v1_funct_2(C_26, A_24, B_25) | ~v1_funct_1(C_26) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.95/2.39  tff(c_4942, plain, (![B_25, C_26]: (k3_funct_2('#skF_3', B_25, C_26, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_26, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_25))) | ~v1_funct_2(C_26, '#skF_3', B_25) | ~v1_funct_1(C_26) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_4930, c_36])).
% 6.95/2.39  tff(c_5049, plain, (![B_485, C_486]: (k3_funct_2('#skF_3', B_485, C_486, '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1(C_486, '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_485))) | ~v1_funct_2(C_486, '#skF_3', B_485) | ~v1_funct_1(C_486))), inference(negUnitSimplification, [status(thm)], [c_68, c_4942])).
% 6.95/2.39  tff(c_5073, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_5049])).
% 6.95/2.39  tff(c_5092, plain, (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_5073])).
% 6.95/2.39  tff(c_5352, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5092, c_58])).
% 6.95/2.39  tff(c_5363, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', '#skF_2', '#skF_5')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4930, c_5352])).
% 6.95/2.39  tff(c_3724, plain, (![C_381, B_382]: (~r2_hidden(k1_funct_1(C_381, '#skF_1'(k1_relat_1(C_381), B_382, C_381)), B_382) | m1_subset_1(C_381, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_381), B_382))) | ~v1_funct_1(C_381) | ~v1_relat_1(C_381))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.95/2.39  tff(c_3727, plain, (![B_382]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_382, '#skF_5')), B_382) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_382))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3058, c_3724])).
% 6.95/2.39  tff(c_3729, plain, (![B_382]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_382, '#skF_5')), B_382) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_382))))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_64, c_3058, c_3727])).
% 6.95/2.39  tff(c_5379, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_5363, c_3729])).
% 6.95/2.39  tff(c_5449, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_5379, c_22])).
% 6.95/2.39  tff(c_5448, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_5379, c_276])).
% 6.95/2.39  tff(c_5495, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5449, c_5448])).
% 6.95/2.39  tff(c_5497, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_5495])).
% 6.95/2.39  tff(c_5498, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3056])).
% 6.95/2.39  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.95/2.39  tff(c_5554, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5498, c_5498, c_4])).
% 6.95/2.39  tff(c_103, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.95/2.39  tff(c_111, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_103])).
% 6.95/2.39  tff(c_5563, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5554, c_111])).
% 6.95/2.39  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.95/2.39  tff(c_5556, plain, (![B_2]: (k2_zfmisc_1('#skF_4', B_2)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5498, c_5498, c_6])).
% 6.95/2.39  tff(c_5613, plain, (![B_508]: (k2_zfmisc_1('#skF_4', B_508)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5498, c_5498, c_6])).
% 6.95/2.39  tff(c_12, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.95/2.39  tff(c_186, plain, (![A_67, B_68, A_5]: (k2_relset_1(A_67, B_68, A_5)=k2_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_67, B_68)))), inference(resolution, [status(thm)], [c_12, c_172])).
% 6.95/2.39  tff(c_5715, plain, (![B_521, A_522]: (k2_relset_1('#skF_4', B_521, A_522)=k2_relat_1(A_522) | ~r1_tarski(A_522, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5613, c_186])).
% 6.95/2.39  tff(c_5727, plain, (![B_523]: (k2_relset_1('#skF_4', B_523, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_5563, c_5715])).
% 6.95/2.39  tff(c_2755, plain, (![A_291, B_292, C_293]: (r1_tarski(k2_relset_1(A_291, B_292, C_293), B_292) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(resolution, [status(thm)], [c_235, c_10])).
% 6.95/2.39  tff(c_2769, plain, (![A_291, B_292, A_5]: (r1_tarski(k2_relset_1(A_291, B_292, A_5), B_292) | ~r1_tarski(A_5, k2_zfmisc_1(A_291, B_292)))), inference(resolution, [status(thm)], [c_12, c_2755])).
% 6.95/2.39  tff(c_5736, plain, (![B_523]: (r1_tarski(k2_relat_1('#skF_5'), B_523) | ~r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', B_523)))), inference(superposition, [status(thm), theory('equality')], [c_5727, c_2769])).
% 6.95/2.39  tff(c_5746, plain, (![B_523]: (r1_tarski(k2_relat_1('#skF_5'), B_523))), inference(demodulation, [status(thm), theory('equality')], [c_5563, c_5556, c_5736])).
% 6.95/2.39  tff(c_5772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5746, c_188])).
% 6.95/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.39  
% 6.95/2.39  Inference rules
% 6.95/2.39  ----------------------
% 6.95/2.39  #Ref     : 0
% 6.95/2.39  #Sup     : 1282
% 6.95/2.39  #Fact    : 0
% 6.95/2.39  #Define  : 0
% 6.95/2.39  #Split   : 15
% 6.95/2.39  #Chain   : 0
% 6.95/2.39  #Close   : 0
% 6.95/2.39  
% 6.95/2.39  Ordering : KBO
% 6.95/2.39  
% 6.95/2.39  Simplification rules
% 6.95/2.39  ----------------------
% 6.95/2.39  #Subsume      : 223
% 6.95/2.39  #Demod        : 701
% 6.95/2.39  #Tautology    : 246
% 6.95/2.39  #SimpNegUnit  : 26
% 6.95/2.39  #BackRed      : 69
% 6.95/2.39  
% 6.95/2.39  #Partial instantiations: 0
% 6.95/2.39  #Strategies tried      : 1
% 6.95/2.39  
% 6.95/2.39  Timing (in seconds)
% 6.95/2.39  ----------------------
% 6.95/2.39  Preprocessing        : 0.34
% 6.95/2.39  Parsing              : 0.18
% 6.95/2.39  CNF conversion       : 0.02
% 6.95/2.39  Main loop            : 1.26
% 6.95/2.39  Inferencing          : 0.44
% 6.95/2.39  Reduction            : 0.38
% 6.95/2.39  Demodulation         : 0.26
% 6.95/2.39  BG Simplification    : 0.06
% 6.95/2.39  Subsumption          : 0.27
% 6.95/2.39  Abstraction          : 0.07
% 6.95/2.39  MUC search           : 0.00
% 6.95/2.39  Cooper               : 0.00
% 6.95/2.39  Total                : 1.64
% 6.95/2.39  Index Insertion      : 0.00
% 6.95/2.39  Index Deletion       : 0.00
% 6.95/2.39  Index Matching       : 0.00
% 6.95/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
