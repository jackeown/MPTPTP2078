%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:57 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 256 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :    7
%              Number of atoms          :  183 (1074 expanded)
%              Number of equality atoms :   26 ( 262 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_29,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_31,plain,(
    ! [B_20,C_21,A_22] :
      ( k1_xboole_0 = B_20
      | v1_partfun1(C_21,A_22)
      | ~ v1_funct_2(C_21,A_22,B_20)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_22,B_20)))
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_31])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_37])).

tff(c_45,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_44])).

tff(c_22,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_31])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_partfun1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_34])).

tff(c_41,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_40])).

tff(c_16,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_46,plain,(
    ! [D_23,C_24,A_25,B_26] :
      ( D_23 = C_24
      | ~ r1_partfun1(C_24,D_23)
      | ~ v1_partfun1(D_23,A_25)
      | ~ v1_partfun1(C_24,A_25)
      | ~ m1_subset_1(D_23,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(D_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    ! [A_25,B_26] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_25)
      | ~ v1_partfun1('#skF_4',A_25)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_46])).

tff(c_51,plain,(
    ! [A_25,B_26] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_25)
      | ~ v1_partfun1('#skF_4',A_25)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_48])).

tff(c_64,plain,(
    ! [A_31,B_32] :
      ( ~ v1_partfun1('#skF_5',A_31)
      | ~ v1_partfun1('#skF_4',A_31)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_67,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_18,c_64])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_45,c_41,c_67])).

tff(c_72,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_12,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_75,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12])).

tff(c_2,plain,(
    ! [D_7,A_1,B_2,C_3] :
      ( k1_funct_1(D_7,'#skF_1'(A_1,B_2,C_3,D_7)) != k1_funct_1(C_3,'#skF_1'(A_1,B_2,C_3,D_7))
      | r2_relset_1(A_1,B_2,C_3,D_7)
      | ~ m1_subset_1(D_7,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_7,A_1,B_2)
      | ~ v1_funct_1(D_7)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_relset_1(A_38,B_39,C_40,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ v1_funct_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ v1_funct_2(C_40,A_38,B_39)
      | ~ v1_funct_1(C_40) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_108,plain,
    ( r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_106])).

tff(c_111,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_108])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_111])).

tff(c_115,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_120,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_114])).

tff(c_132,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_24])).

tff(c_125,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_26])).

tff(c_6,plain,(
    ! [C_11,B_10] :
      ( v1_partfun1(C_11,k1_xboole_0)
      | ~ v1_funct_2(C_11,k1_xboole_0,B_10)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_10)))
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,(
    ! [C_41,B_42] :
      ( v1_partfun1(C_41,'#skF_3')
      | ~ v1_funct_2(C_41,'#skF_3',B_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_42)))
      | ~ v1_funct_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_115,c_115,c_6])).

tff(c_141,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_135])).

tff(c_147,plain,(
    v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_125,c_141])).

tff(c_130,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_20])).

tff(c_133,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_18])).

tff(c_138,plain,
    ( v1_partfun1('#skF_5','#skF_3')
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_135])).

tff(c_144,plain,(
    v1_partfun1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_130,c_138])).

tff(c_164,plain,(
    ! [D_46,C_47,A_48,B_49] :
      ( D_46 = C_47
      | ~ r1_partfun1(C_47,D_46)
      | ~ v1_partfun1(D_46,A_48)
      | ~ v1_partfun1(C_47,A_48)
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(D_46)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_166,plain,(
    ! [A_48,B_49] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_48)
      | ~ v1_partfun1('#skF_4',A_48)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_164])).

tff(c_169,plain,(
    ! [A_48,B_49] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_48)
      | ~ v1_partfun1('#skF_4',A_48)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_166])).

tff(c_171,plain,(
    ! [A_50,B_51] :
      ( ~ v1_partfun1('#skF_5',A_50)
      | ~ v1_partfun1('#skF_4',A_50)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_174,plain,
    ( ~ v1_partfun1('#skF_5','#skF_3')
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_133,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_147,c_144,c_174])).

tff(c_179,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_131,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_12])).

tff(c_182,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_131])).

tff(c_218,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_relset_1(A_61,B_62,C_63,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(C_63,A_61,B_62)
      | ~ v1_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(C_63,A_61,B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2])).

tff(c_220,plain,
    ( r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_132,c_218])).

tff(c_223,plain,(
    r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_125,c_132,c_220])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_223])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:08:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  
% 2.31/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.29  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.31/1.29  
% 2.31/1.29  %Foreground sorts:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Background operators:
% 2.31/1.29  
% 2.31/1.29  
% 2.31/1.29  %Foreground operators:
% 2.31/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.31/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.31/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.31/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.31/1.29  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.31/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.29  
% 2.31/1.31  tff(f_102, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 2.31/1.31  tff(f_62, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.31/1.31  tff(f_79, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.31/1.31  tff(f_45, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_funct_2)).
% 2.31/1.31  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_14, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_29, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 2.31/1.31  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_26, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_31, plain, (![B_20, C_21, A_22]: (k1_xboole_0=B_20 | v1_partfun1(C_21, A_22) | ~v1_funct_2(C_21, A_22, B_20) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_22, B_20))) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.31  tff(c_37, plain, (k1_xboole_0='#skF_3' | v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_31])).
% 2.31/1.31  tff(c_44, plain, (k1_xboole_0='#skF_3' | v1_partfun1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_37])).
% 2.31/1.31  tff(c_45, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_29, c_44])).
% 2.31/1.31  tff(c_22, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_20, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_18, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_34, plain, (k1_xboole_0='#skF_3' | v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_31])).
% 2.31/1.31  tff(c_40, plain, (k1_xboole_0='#skF_3' | v1_partfun1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_34])).
% 2.31/1.31  tff(c_41, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_29, c_40])).
% 2.31/1.31  tff(c_16, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_46, plain, (![D_23, C_24, A_25, B_26]: (D_23=C_24 | ~r1_partfun1(C_24, D_23) | ~v1_partfun1(D_23, A_25) | ~v1_partfun1(C_24, A_25) | ~m1_subset_1(D_23, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(D_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.31  tff(c_48, plain, (![A_25, B_26]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_25) | ~v1_partfun1('#skF_4', A_25) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_46])).
% 2.31/1.31  tff(c_51, plain, (![A_25, B_26]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_25) | ~v1_partfun1('#skF_4', A_25) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_48])).
% 2.31/1.31  tff(c_64, plain, (![A_31, B_32]: (~v1_partfun1('#skF_5', A_31) | ~v1_partfun1('#skF_4', A_31) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(splitLeft, [status(thm)], [c_51])).
% 2.31/1.31  tff(c_67, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_18, c_64])).
% 2.31/1.31  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_45, c_41, c_67])).
% 2.31/1.31  tff(c_72, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_51])).
% 2.31/1.31  tff(c_12, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.31  tff(c_75, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12])).
% 2.31/1.31  tff(c_2, plain, (![D_7, A_1, B_2, C_3]: (k1_funct_1(D_7, '#skF_1'(A_1, B_2, C_3, D_7))!=k1_funct_1(C_3, '#skF_1'(A_1, B_2, C_3, D_7)) | r2_relset_1(A_1, B_2, C_3, D_7) | ~m1_subset_1(D_7, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_7, A_1, B_2) | ~v1_funct_1(D_7) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.31/1.31  tff(c_106, plain, (![A_38, B_39, C_40]: (r2_relset_1(A_38, B_39, C_40, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(C_40, A_38, B_39) | ~v1_funct_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))) | ~v1_funct_2(C_40, A_38, B_39) | ~v1_funct_1(C_40))), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 2.31/1.31  tff(c_108, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_106])).
% 2.31/1.31  tff(c_111, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_108])).
% 2.31/1.31  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_111])).
% 2.31/1.31  tff(c_115, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 2.31/1.31  tff(c_114, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14])).
% 2.31/1.31  tff(c_120, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_114])).
% 2.31/1.31  tff(c_132, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_24])).
% 2.31/1.31  tff(c_125, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_26])).
% 2.31/1.31  tff(c_6, plain, (![C_11, B_10]: (v1_partfun1(C_11, k1_xboole_0) | ~v1_funct_2(C_11, k1_xboole_0, B_10) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_10))) | ~v1_funct_1(C_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.31  tff(c_135, plain, (![C_41, B_42]: (v1_partfun1(C_41, '#skF_3') | ~v1_funct_2(C_41, '#skF_3', B_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_42))) | ~v1_funct_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_115, c_115, c_6])).
% 2.31/1.31  tff(c_141, plain, (v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_135])).
% 2.31/1.31  tff(c_147, plain, (v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_125, c_141])).
% 2.31/1.31  tff(c_130, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_20])).
% 2.31/1.31  tff(c_133, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_18])).
% 2.31/1.31  tff(c_138, plain, (v1_partfun1('#skF_5', '#skF_3') | ~v1_funct_2('#skF_5', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_133, c_135])).
% 2.31/1.31  tff(c_144, plain, (v1_partfun1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_130, c_138])).
% 2.31/1.31  tff(c_164, plain, (![D_46, C_47, A_48, B_49]: (D_46=C_47 | ~r1_partfun1(C_47, D_46) | ~v1_partfun1(D_46, A_48) | ~v1_partfun1(C_47, A_48) | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1(D_46) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.31  tff(c_166, plain, (![A_48, B_49]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_48) | ~v1_partfun1('#skF_4', A_48) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_164])).
% 2.31/1.31  tff(c_169, plain, (![A_48, B_49]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_48) | ~v1_partfun1('#skF_4', A_48) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_166])).
% 2.31/1.31  tff(c_171, plain, (![A_50, B_51]: (~v1_partfun1('#skF_5', A_50) | ~v1_partfun1('#skF_4', A_50) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(splitLeft, [status(thm)], [c_169])).
% 2.31/1.31  tff(c_174, plain, (~v1_partfun1('#skF_5', '#skF_3') | ~v1_partfun1('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_133, c_171])).
% 2.31/1.31  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_147, c_144, c_174])).
% 2.31/1.31  tff(c_179, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_169])).
% 2.31/1.31  tff(c_131, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_12])).
% 2.31/1.31  tff(c_182, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_131])).
% 2.31/1.31  tff(c_218, plain, (![A_61, B_62, C_63]: (r2_relset_1(A_61, B_62, C_63, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(C_63, A_61, B_62) | ~v1_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(C_63, A_61, B_62) | ~v1_funct_1(C_63))), inference(reflexivity, [status(thm), theory('equality')], [c_2])).
% 2.31/1.31  tff(c_220, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_132, c_218])).
% 2.31/1.31  tff(c_223, plain, (r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_125, c_132, c_220])).
% 2.31/1.31  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_223])).
% 2.31/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.31  
% 2.31/1.31  Inference rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Ref     : 2
% 2.31/1.31  #Sup     : 29
% 2.31/1.31  #Fact    : 0
% 2.31/1.31  #Define  : 0
% 2.31/1.31  #Split   : 3
% 2.31/1.31  #Chain   : 0
% 2.31/1.31  #Close   : 0
% 2.31/1.31  
% 2.31/1.31  Ordering : KBO
% 2.31/1.31  
% 2.31/1.31  Simplification rules
% 2.31/1.31  ----------------------
% 2.31/1.31  #Subsume      : 1
% 2.31/1.31  #Demod        : 72
% 2.31/1.31  #Tautology    : 22
% 2.31/1.31  #SimpNegUnit  : 6
% 2.31/1.31  #BackRed      : 14
% 2.31/1.31  
% 2.31/1.31  #Partial instantiations: 0
% 2.31/1.31  #Strategies tried      : 1
% 2.31/1.31  
% 2.31/1.31  Timing (in seconds)
% 2.31/1.31  ----------------------
% 2.31/1.31  Preprocessing        : 0.32
% 2.31/1.31  Parsing              : 0.17
% 2.31/1.31  CNF conversion       : 0.02
% 2.31/1.31  Main loop            : 0.22
% 2.31/1.31  Inferencing          : 0.08
% 2.31/1.31  Reduction            : 0.07
% 2.31/1.31  Demodulation         : 0.05
% 2.31/1.31  BG Simplification    : 0.01
% 2.31/1.31  Subsumption          : 0.03
% 2.31/1.31  Abstraction          : 0.01
% 2.31/1.31  MUC search           : 0.00
% 2.31/1.31  Cooper               : 0.00
% 2.31/1.31  Total                : 0.59
% 2.31/1.31  Index Insertion      : 0.00
% 2.31/1.31  Index Deletion       : 0.00
% 2.31/1.31  Index Matching       : 0.00
% 2.31/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
