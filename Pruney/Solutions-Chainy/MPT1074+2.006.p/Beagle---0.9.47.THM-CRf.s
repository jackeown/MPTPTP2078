%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:07 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 550 expanded)
%              Number of leaves         :   37 ( 208 expanded)
%              Depth                    :   19
%              Number of atoms          :  165 (1817 expanded)
%              Number of equality atoms :   27 ( 344 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
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

tff(f_102,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_64,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_60])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_87,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_91,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_87])).

tff(c_46,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_92,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_46])).

tff(c_99,plain,
    ( ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_102,plain,(
    ~ v5_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_99])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_103,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_107,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_103])).

tff(c_116,plain,(
    ! [B_70,A_71,C_72] :
      ( k1_xboole_0 = B_70
      | k1_relset_1(A_71,B_70,C_72) = A_71
      | ~ v1_funct_2(C_72,A_71,B_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_116])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_107,c_119])).

tff(c_123,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_179,plain,(
    ! [C_85,B_86] :
      ( r2_hidden('#skF_1'(k1_relat_1(C_85),B_86,C_85),k1_relat_1(C_85))
      | m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_85),B_86)))
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_185,plain,(
    ! [B_86] :
      ( r2_hidden('#skF_1'('#skF_3',B_86,'#skF_5'),k1_relat_1('#skF_5'))
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_86)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_179])).

tff(c_194,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_1'('#skF_3',B_87,'#skF_5'),'#skF_3')
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_123,c_123,c_185])).

tff(c_12,plain,(
    ! [C_10,B_9,A_8] :
      ( v5_relat_1(C_10,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_231,plain,(
    ! [B_88] :
      ( v5_relat_1('#skF_5',B_88)
      | r2_hidden('#skF_1'('#skF_3',B_88,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_194,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_235,plain,(
    ! [B_88] :
      ( m1_subset_1('#skF_1'('#skF_3',B_88,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_88) ) ),
    inference(resolution,[status(thm)],[c_231,c_4])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_268,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k3_funct_2(A_99,B_100,C_101,D_102) = k1_funct_1(C_101,D_102)
      | ~ m1_subset_1(D_102,A_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_2(C_101,A_99,B_100)
      | ~ v1_funct_1(C_101)
      | v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_276,plain,(
    ! [B_100,C_101,B_88] :
      ( k3_funct_2('#skF_3',B_100,C_101,'#skF_1'('#skF_3',B_88,'#skF_5')) = k1_funct_1(C_101,'#skF_1'('#skF_3',B_88,'#skF_5'))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_100)))
      | ~ v1_funct_2(C_101,'#skF_3',B_100)
      | ~ v1_funct_1(C_101)
      | v1_xboole_0('#skF_3')
      | v5_relat_1('#skF_5',B_88) ) ),
    inference(resolution,[status(thm)],[c_235,c_268])).

tff(c_344,plain,(
    ! [B_104,C_105,B_106] :
      ( k3_funct_2('#skF_3',B_104,C_105,'#skF_1'('#skF_3',B_106,'#skF_5')) = k1_funct_1(C_105,'#skF_1'('#skF_3',B_106,'#skF_5'))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_104)))
      | ~ v1_funct_2(C_105,'#skF_3',B_104)
      | ~ v1_funct_1(C_105)
      | v5_relat_1('#skF_5',B_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_276])).

tff(c_350,plain,(
    ! [B_106] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_106,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_106,'#skF_5'))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v5_relat_1('#skF_5',B_106) ) ),
    inference(resolution,[status(thm)],[c_50,c_344])).

tff(c_376,plain,(
    ! [B_110] :
      ( k3_funct_2('#skF_3','#skF_4','#skF_5','#skF_1'('#skF_3',B_110,'#skF_5')) = k1_funct_1('#skF_5','#skF_1'('#skF_3',B_110,'#skF_5'))
      | v5_relat_1('#skF_5',B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_350])).

tff(c_48,plain,(
    ! [E_39] :
      ( r2_hidden(k3_funct_2('#skF_3','#skF_4','#skF_5',E_39),'#skF_2')
      | ~ m1_subset_1(E_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_395,plain,(
    ! [B_112] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_112,'#skF_5')),'#skF_2')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_112,'#skF_5'),'#skF_3')
      | v5_relat_1('#skF_5',B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_48])).

tff(c_172,plain,(
    ! [C_82,B_83] :
      ( ~ r2_hidden(k1_funct_1(C_82,'#skF_1'(k1_relat_1(C_82),B_83,C_82)),B_83)
      | v1_funct_2(C_82,k1_relat_1(C_82),B_83)
      | ~ v1_funct_1(C_82)
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_175,plain,(
    ! [B_83] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_83,'#skF_5')),B_83)
      | v1_funct_2('#skF_5',k1_relat_1('#skF_5'),B_83)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_172])).

tff(c_177,plain,(
    ! [B_83] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_83,'#skF_5')),B_83)
      | v1_funct_2('#skF_5','#skF_3',B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_123,c_175])).

tff(c_403,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_395,c_177])).

tff(c_412,plain,
    ( v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_403])).

tff(c_414,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_423,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_235,c_414])).

tff(c_432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_423])).

tff(c_434,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_242,plain,(
    ! [C_91,B_92] :
      ( ~ r2_hidden(k1_funct_1(C_91,'#skF_1'(k1_relat_1(C_91),B_92,C_91)),B_92)
      | m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_91),B_92)))
      | ~ v1_funct_1(C_91)
      | ~ v1_relat_1(C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_245,plain,(
    ! [B_92] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_92,'#skF_5')),B_92)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'),B_92)))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_242])).

tff(c_247,plain,(
    ! [B_92] :
      ( ~ r2_hidden(k1_funct_1('#skF_5','#skF_1'('#skF_3',B_92,'#skF_5')),B_92)
      | m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_92))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_123,c_245])).

tff(c_399,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3')
    | v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_395,c_247])).

tff(c_409,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_5'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_399])).

tff(c_461,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_409])).

tff(c_485,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_461,c_12])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_485])).

tff(c_514,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_521,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_2])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_521])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:17:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.44  
% 2.69/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.69/1.44  
% 2.69/1.44  %Foreground sorts:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Background operators:
% 2.69/1.44  
% 2.69/1.44  
% 2.69/1.44  %Foreground operators:
% 2.69/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.69/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.69/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.69/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.69/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.69/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.69/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.44  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.69/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.44  
% 2.69/1.46  tff(f_124, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 2.69/1.46  tff(f_40, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.69/1.46  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.69/1.46  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.69/1.46  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.69/1.46  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.69/1.46  tff(f_102, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 2.69/1.46  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.69/1.46  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.69/1.46  tff(f_85, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.69/1.46  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.46  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.46  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.46  tff(c_60, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.69/1.46  tff(c_64, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_60])).
% 2.69/1.46  tff(c_8, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.69/1.46  tff(c_87, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.46  tff(c_91, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_87])).
% 2.69/1.46  tff(c_46, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.46  tff(c_92, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_46])).
% 2.69/1.46  tff(c_99, plain, (~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_92])).
% 2.69/1.46  tff(c_102, plain, (~v5_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_99])).
% 2.69/1.46  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.46  tff(c_52, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.46  tff(c_103, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.69/1.46  tff(c_107, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_103])).
% 2.69/1.46  tff(c_116, plain, (![B_70, A_71, C_72]: (k1_xboole_0=B_70 | k1_relset_1(A_71, B_70, C_72)=A_71 | ~v1_funct_2(C_72, A_71, B_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.69/1.46  tff(c_119, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_116])).
% 2.69/1.46  tff(c_122, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_107, c_119])).
% 2.69/1.46  tff(c_123, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_122])).
% 2.69/1.46  tff(c_179, plain, (![C_85, B_86]: (r2_hidden('#skF_1'(k1_relat_1(C_85), B_86, C_85), k1_relat_1(C_85)) | m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_85), B_86))) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.46  tff(c_185, plain, (![B_86]: (r2_hidden('#skF_1'('#skF_3', B_86, '#skF_5'), k1_relat_1('#skF_5')) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_86))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_179])).
% 2.69/1.46  tff(c_194, plain, (![B_87]: (r2_hidden('#skF_1'('#skF_3', B_87, '#skF_5'), '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_123, c_123, c_185])).
% 2.69/1.46  tff(c_12, plain, (![C_10, B_9, A_8]: (v5_relat_1(C_10, B_9) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.46  tff(c_231, plain, (![B_88]: (v5_relat_1('#skF_5', B_88) | r2_hidden('#skF_1'('#skF_3', B_88, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_194, c_12])).
% 2.69/1.46  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.69/1.46  tff(c_235, plain, (![B_88]: (m1_subset_1('#skF_1'('#skF_3', B_88, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_88))), inference(resolution, [status(thm)], [c_231, c_4])).
% 2.69/1.46  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.46  tff(c_268, plain, (![A_99, B_100, C_101, D_102]: (k3_funct_2(A_99, B_100, C_101, D_102)=k1_funct_1(C_101, D_102) | ~m1_subset_1(D_102, A_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_2(C_101, A_99, B_100) | ~v1_funct_1(C_101) | v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.69/1.46  tff(c_276, plain, (![B_100, C_101, B_88]: (k3_funct_2('#skF_3', B_100, C_101, '#skF_1'('#skF_3', B_88, '#skF_5'))=k1_funct_1(C_101, '#skF_1'('#skF_3', B_88, '#skF_5')) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_100))) | ~v1_funct_2(C_101, '#skF_3', B_100) | ~v1_funct_1(C_101) | v1_xboole_0('#skF_3') | v5_relat_1('#skF_5', B_88))), inference(resolution, [status(thm)], [c_235, c_268])).
% 2.69/1.46  tff(c_344, plain, (![B_104, C_105, B_106]: (k3_funct_2('#skF_3', B_104, C_105, '#skF_1'('#skF_3', B_106, '#skF_5'))=k1_funct_1(C_105, '#skF_1'('#skF_3', B_106, '#skF_5')) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_104))) | ~v1_funct_2(C_105, '#skF_3', B_104) | ~v1_funct_1(C_105) | v5_relat_1('#skF_5', B_106))), inference(negUnitSimplification, [status(thm)], [c_58, c_276])).
% 2.69/1.46  tff(c_350, plain, (![B_106]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_106, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_106, '#skF_5')) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v5_relat_1('#skF_5', B_106))), inference(resolution, [status(thm)], [c_50, c_344])).
% 2.69/1.46  tff(c_376, plain, (![B_110]: (k3_funct_2('#skF_3', '#skF_4', '#skF_5', '#skF_1'('#skF_3', B_110, '#skF_5'))=k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_110, '#skF_5')) | v5_relat_1('#skF_5', B_110))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_350])).
% 2.69/1.46  tff(c_48, plain, (![E_39]: (r2_hidden(k3_funct_2('#skF_3', '#skF_4', '#skF_5', E_39), '#skF_2') | ~m1_subset_1(E_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.69/1.46  tff(c_395, plain, (![B_112]: (r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_112, '#skF_5')), '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', B_112, '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', B_112))), inference(superposition, [status(thm), theory('equality')], [c_376, c_48])).
% 2.69/1.46  tff(c_172, plain, (![C_82, B_83]: (~r2_hidden(k1_funct_1(C_82, '#skF_1'(k1_relat_1(C_82), B_83, C_82)), B_83) | v1_funct_2(C_82, k1_relat_1(C_82), B_83) | ~v1_funct_1(C_82) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.46  tff(c_175, plain, (![B_83]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_83, '#skF_5')), B_83) | v1_funct_2('#skF_5', k1_relat_1('#skF_5'), B_83) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_172])).
% 2.69/1.46  tff(c_177, plain, (![B_83]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_83, '#skF_5')), B_83) | v1_funct_2('#skF_5', '#skF_3', B_83))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_123, c_175])).
% 2.69/1.46  tff(c_403, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_395, c_177])).
% 2.69/1.46  tff(c_412, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_102, c_403])).
% 2.69/1.46  tff(c_414, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_412])).
% 2.69/1.46  tff(c_423, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_235, c_414])).
% 2.69/1.46  tff(c_432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_423])).
% 2.69/1.46  tff(c_434, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(splitRight, [status(thm)], [c_412])).
% 2.69/1.46  tff(c_242, plain, (![C_91, B_92]: (~r2_hidden(k1_funct_1(C_91, '#skF_1'(k1_relat_1(C_91), B_92, C_91)), B_92) | m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_91), B_92))) | ~v1_funct_1(C_91) | ~v1_relat_1(C_91))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.69/1.46  tff(c_245, plain, (![B_92]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_92, '#skF_5')), B_92) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_5'), B_92))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_242])).
% 2.69/1.46  tff(c_247, plain, (![B_92]: (~r2_hidden(k1_funct_1('#skF_5', '#skF_1'('#skF_3', B_92, '#skF_5')), B_92) | m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_92))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_123, c_245])).
% 2.69/1.46  tff(c_399, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3') | v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_395, c_247])).
% 2.69/1.46  tff(c_409, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_5'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_102, c_399])).
% 2.69/1.46  tff(c_461, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_434, c_409])).
% 2.69/1.46  tff(c_485, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_461, c_12])).
% 2.69/1.46  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_485])).
% 2.69/1.46  tff(c_514, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_122])).
% 2.69/1.46  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.69/1.46  tff(c_521, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_2])).
% 2.69/1.46  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_521])).
% 2.69/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.46  
% 2.69/1.46  Inference rules
% 2.69/1.46  ----------------------
% 2.69/1.46  #Ref     : 0
% 2.69/1.46  #Sup     : 93
% 2.69/1.46  #Fact    : 0
% 2.69/1.46  #Define  : 0
% 2.69/1.46  #Split   : 4
% 2.69/1.46  #Chain   : 0
% 2.69/1.46  #Close   : 0
% 2.69/1.46  
% 2.69/1.46  Ordering : KBO
% 2.69/1.46  
% 2.69/1.46  Simplification rules
% 2.69/1.46  ----------------------
% 2.69/1.46  #Subsume      : 14
% 2.69/1.46  #Demod        : 92
% 2.69/1.46  #Tautology    : 19
% 2.69/1.46  #SimpNegUnit  : 10
% 2.69/1.46  #BackRed      : 8
% 2.69/1.46  
% 2.69/1.46  #Partial instantiations: 0
% 2.69/1.46  #Strategies tried      : 1
% 2.69/1.46  
% 2.69/1.46  Timing (in seconds)
% 2.69/1.46  ----------------------
% 2.69/1.46  Preprocessing        : 0.35
% 2.69/1.46  Parsing              : 0.19
% 2.69/1.46  CNF conversion       : 0.02
% 2.69/1.46  Main loop            : 0.32
% 2.69/1.46  Inferencing          : 0.12
% 2.69/1.46  Reduction            : 0.10
% 2.69/1.46  Demodulation         : 0.07
% 2.69/1.46  BG Simplification    : 0.02
% 2.69/1.46  Subsumption          : 0.06
% 2.69/1.46  Abstraction          : 0.02
% 2.69/1.46  MUC search           : 0.00
% 2.69/1.46  Cooper               : 0.00
% 2.69/1.46  Total                : 0.72
% 2.69/1.46  Index Insertion      : 0.00
% 2.69/1.46  Index Deletion       : 0.00
% 2.69/1.46  Index Matching       : 0.00
% 2.69/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
