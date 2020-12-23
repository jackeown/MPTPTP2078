%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1068+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:21 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 148 expanded)
%              Number of leaves         :   34 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 584 expanded)
%              Number of equality atoms :   40 ( 129 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_46,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(c_22,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_58,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_26,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,B_23)
      | v1_xboole_0(B_23)
      | ~ m1_subset_1(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_113,plain,(
    ! [E_55,A_56,C_58,D_57,B_54] :
      ( k1_funct_1(k5_relat_1(D_57,E_55),C_58) = k1_funct_1(E_55,k1_funct_1(D_57,C_58))
      | k1_xboole_0 = B_54
      | ~ r2_hidden(C_58,A_56)
      | ~ v1_funct_1(E_55)
      | ~ v1_relat_1(E_55)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_56,B_54)))
      | ~ v1_funct_2(D_57,A_56,B_54)
      | ~ v1_funct_1(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_117,plain,(
    ! [B_63,B_62,A_59,D_61,E_60] :
      ( k1_funct_1(k5_relat_1(D_61,E_60),A_59) = k1_funct_1(E_60,k1_funct_1(D_61,A_59))
      | k1_xboole_0 = B_63
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(B_62,B_63)))
      | ~ v1_funct_2(D_61,B_62,B_63)
      | ~ v1_funct_1(D_61)
      | v1_xboole_0(B_62)
      | ~ m1_subset_1(A_59,B_62) ) ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_119,plain,(
    ! [E_60,A_59] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_60),A_59) = k1_funct_1(E_60,k1_funct_1('#skF_4',A_59))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_59,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_124,plain,(
    ! [E_60,A_59] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_60),A_59) = k1_funct_1(E_60,k1_funct_1('#skF_4',A_59))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_59,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_119])).

tff(c_129,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_14,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_132,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_129,c_14])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_132])).

tff(c_137,plain,(
    ! [E_60,A_59] :
      ( k1_xboole_0 = '#skF_3'
      | k1_funct_1(k5_relat_1('#skF_4',E_60),A_59) = k1_funct_1(E_60,k1_funct_1('#skF_4',A_59))
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ m1_subset_1(A_59,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_140,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_6,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_35,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_39,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_6])).

tff(c_143,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_40])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_143])).

tff(c_164,plain,(
    ! [E_69,A_70] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_69),A_70) = k1_funct_1(E_69,k1_funct_1('#skF_4',A_70))
      | ~ v1_funct_1(E_69)
      | ~ v1_relat_1(E_69)
      | ~ m1_subset_1(A_70,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_150,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_60,plain,(
    ! [F_46,E_43,C_47,D_45,A_44,B_42] :
      ( k1_partfun1(A_44,B_42,C_47,D_45,E_43,F_46) = k5_relat_1(E_43,F_46)
      | ~ m1_subset_1(F_46,k1_zfmisc_1(k2_zfmisc_1(C_47,D_45)))
      | ~ v1_funct_1(F_46)
      | ~ m1_subset_1(E_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_42)))
      | ~ v1_funct_1(E_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_64,plain,(
    ! [A_44,B_42,E_43] :
      ( k1_partfun1(A_44,B_42,'#skF_3','#skF_1',E_43,'#skF_5') = k5_relat_1(E_43,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_42)))
      | ~ v1_funct_1(E_43) ) ),
    inference(resolution,[status(thm)],[c_24,c_60])).

tff(c_92,plain,(
    ! [A_51,B_52,E_53] :
      ( k1_partfun1(A_51,B_52,'#skF_3','#skF_1',E_53,'#skF_5') = k5_relat_1(E_53,'#skF_5')
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ v1_funct_1(E_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_64])).

tff(c_95,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_92])).

tff(c_101,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_95])).

tff(c_20,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_151,plain,(
    ! [D_66,B_64,C_65,A_67,E_68] :
      ( k1_partfun1(A_67,B_64,B_64,C_65,D_66,E_68) = k8_funct_2(A_67,B_64,C_65,D_66,E_68)
      | k1_xboole_0 = B_64
      | ~ r1_tarski(k2_relset_1(A_67,B_64,D_66),k1_relset_1(B_64,C_65,E_68))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(B_64,C_65)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_64)))
      | ~ v1_funct_2(D_66,A_67,B_64)
      | ~ v1_funct_1(D_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_154,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_151])).

tff(c_157,plain,
    ( k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_24,c_101,c_154])).

tff(c_158,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_157])).

tff(c_16,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_159,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_16])).

tff(c_170,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_159])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_58,c_26,c_170])).

%------------------------------------------------------------------------------
