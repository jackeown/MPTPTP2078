%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:53 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 519 expanded)
%              Number of leaves         :   43 ( 199 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 (1707 expanded)
%              Number of equality atoms :   41 ( 185 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,A,B)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & v1_funct_2(E,B,C)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
                   => ( ( v2_funct_2(D,B)
                        & v2_funct_2(E,C) )
                     => v2_funct_2(k1_partfun1(A,B,B,C,D,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_funct_2)).

tff(f_58,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_24,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_116,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_116])).

tff(c_132,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_125])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    v2_funct_2('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_231,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_244,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_231])).

tff(c_403,plain,(
    ! [B_111,A_112] :
      ( k2_relat_1(B_111) = A_112
      | ~ v2_funct_2(B_111,A_112)
      | ~ v5_relat_1(B_111,A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_415,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v2_funct_2('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_244,c_403])).

tff(c_429,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_62,c_415])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_515,plain,(
    ! [A_116,B_117,C_118] :
      ( k1_relset_1(A_116,B_117,C_118) = k1_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_528,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_515])).

tff(c_1136,plain,(
    ! [B_188,A_189,C_190] :
      ( k1_xboole_0 = B_188
      | k1_relset_1(A_189,B_188,C_190) = A_189
      | ~ v1_funct_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1146,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1136])).

tff(c_1153,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_528,c_1146])).

tff(c_1175,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1153])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_122,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_116])).

tff(c_129,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_122])).

tff(c_64,plain,(
    v2_funct_2('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_243,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_231])).

tff(c_418,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v2_funct_2('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_243,c_403])).

tff(c_432,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_64,c_418])).

tff(c_773,plain,(
    ! [B_135,A_136] :
      ( k2_relat_1(k5_relat_1(B_135,A_136)) = k2_relat_1(A_136)
      | ~ r1_tarski(k1_relat_1(A_136),k2_relat_1(B_135))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_779,plain,(
    ! [A_136] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_136)) = k2_relat_1(A_136)
      | ~ r1_tarski(k1_relat_1(A_136),'#skF_3')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_773])).

tff(c_789,plain,(
    ! [A_136] :
      ( k2_relat_1(k5_relat_1('#skF_5',A_136)) = k2_relat_1(A_136)
      | ~ r1_tarski(k1_relat_1(A_136),'#skF_3')
      | ~ v1_relat_1(A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_779])).

tff(c_1183,plain,
    ( k2_relat_1(k5_relat_1('#skF_5','#skF_6')) = k2_relat_1('#skF_6')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_789])).

tff(c_1192,plain,(
    k2_relat_1(k5_relat_1('#skF_5','#skF_6')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_10,c_429,c_1183])).

tff(c_314,plain,(
    ! [B_107,A_108] :
      ( r1_tarski(k2_relat_1(B_107),A_108)
      | ~ v5_relat_1(B_107,A_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [B_66,A_67] :
      ( ~ r1_tarski(B_66,A_67)
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_350,plain,(
    ! [B_107] :
      ( v1_xboole_0(k2_relat_1(B_107))
      | ~ v5_relat_1(B_107,'#skF_1'(k2_relat_1(B_107)))
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_314,c_95])).

tff(c_1227,plain,
    ( v1_xboole_0(k2_relat_1(k5_relat_1('#skF_5','#skF_6')))
    | ~ v5_relat_1(k5_relat_1('#skF_5','#skF_6'),'#skF_1'('#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_350])).

tff(c_1242,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v5_relat_1(k5_relat_1('#skF_5','#skF_6'),'#skF_1'('#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1192,c_1227])).

tff(c_1243,plain,
    ( ~ v5_relat_1(k5_relat_1('#skF_5','#skF_6'),'#skF_1'('#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1242])).

tff(c_1246,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1243])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1325,plain,(
    ! [B_209,E_207,D_208,A_210,C_212,F_211] :
      ( k1_partfun1(A_210,B_209,C_212,D_208,E_207,F_211) = k5_relat_1(E_207,F_211)
      | ~ m1_subset_1(F_211,k1_zfmisc_1(k2_zfmisc_1(C_212,D_208)))
      | ~ v1_funct_1(F_211)
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209)))
      | ~ v1_funct_1(E_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1332,plain,(
    ! [A_210,B_209,E_207] :
      ( k1_partfun1(A_210,B_209,'#skF_3','#skF_4',E_207,'#skF_6') = k5_relat_1(E_207,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_207,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209)))
      | ~ v1_funct_1(E_207) ) ),
    inference(resolution,[status(thm)],[c_66,c_1325])).

tff(c_1539,plain,(
    ! [A_234,B_235,E_236] :
      ( k1_partfun1(A_234,B_235,'#skF_3','#skF_4',E_236,'#skF_6') = k5_relat_1(E_236,'#skF_6')
      | ~ m1_subset_1(E_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_1(E_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1332])).

tff(c_1549,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_1539])).

tff(c_1557,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1549])).

tff(c_54,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] :
      ( m1_subset_1(k1_partfun1(A_36,B_37,C_38,D_39,E_40,F_41),k1_zfmisc_1(k2_zfmisc_1(A_36,D_39)))
      | ~ m1_subset_1(F_41,k1_zfmisc_1(k2_zfmisc_1(C_38,D_39)))
      | ~ v1_funct_1(F_41)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(E_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1566,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_54])).

tff(c_1570,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1566])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1602,plain,(
    v1_relat_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1570,c_30])).

tff(c_1632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1246,c_1602])).

tff(c_1634,plain,(
    v1_relat_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1243])).

tff(c_283,plain,(
    ! [B_98,A_99] :
      ( v5_relat_1(B_98,A_99)
      | ~ r1_tarski(k2_relat_1(B_98),A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_288,plain,(
    ! [B_98] :
      ( v5_relat_1(B_98,k2_relat_1(B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_10,c_283])).

tff(c_366,plain,(
    ! [B_110] :
      ( v2_funct_2(B_110,k2_relat_1(B_110))
      | ~ v5_relat_1(B_110,k2_relat_1(B_110))
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_374,plain,(
    ! [B_98] :
      ( v2_funct_2(B_98,k2_relat_1(B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_288,c_366])).

tff(c_1230,plain,
    ( v2_funct_2(k5_relat_1('#skF_5','#skF_6'),'#skF_4')
    | ~ v1_relat_1(k5_relat_1('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1192,c_374])).

tff(c_1686,plain,(
    v2_funct_2(k5_relat_1('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1230])).

tff(c_1670,plain,(
    ! [B_248,F_250,D_247,E_246,A_249,C_251] :
      ( k1_partfun1(A_249,B_248,C_251,D_247,E_246,F_250) = k5_relat_1(E_246,F_250)
      | ~ m1_subset_1(F_250,k1_zfmisc_1(k2_zfmisc_1(C_251,D_247)))
      | ~ v1_funct_1(F_250)
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248)))
      | ~ v1_funct_1(E_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1677,plain,(
    ! [A_249,B_248,E_246] :
      ( k1_partfun1(A_249,B_248,'#skF_3','#skF_4',E_246,'#skF_6') = k5_relat_1(E_246,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248)))
      | ~ v1_funct_1(E_246) ) ),
    inference(resolution,[status(thm)],[c_66,c_1670])).

tff(c_2168,plain,(
    ! [A_275,B_276,E_277] :
      ( k1_partfun1(A_275,B_276,'#skF_3','#skF_4',E_277,'#skF_6') = k5_relat_1(E_277,'#skF_6')
      | ~ m1_subset_1(E_277,k1_zfmisc_1(k2_zfmisc_1(A_275,B_276)))
      | ~ v1_funct_1(E_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1677])).

tff(c_2184,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_2168])).

tff(c_2198,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2184])).

tff(c_60,plain,(
    ~ v2_funct_2(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2243,plain,(
    ~ v2_funct_2(k5_relat_1('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2198,c_60])).

tff(c_2246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1686,c_2243])).

tff(c_2247,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1153])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_96,plain,(
    ! [A_68] :
      ( ~ r1_tarski(A_68,'#skF_1'(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_101,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_2287,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2247,c_101])).

tff(c_2290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:30:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.73  
% 4.48/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.73  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 4.48/1.73  
% 4.48/1.73  %Foreground sorts:
% 4.48/1.73  
% 4.48/1.73  
% 4.48/1.73  %Background operators:
% 4.48/1.73  
% 4.48/1.73  
% 4.48/1.73  %Foreground operators:
% 4.48/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.48/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.48/1.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.48/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.48/1.73  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.48/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.48/1.73  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.48/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.48/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.48/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.48/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.73  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.48/1.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.48/1.73  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.48/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.48/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.48/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.73  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.48/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.48/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.48/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.73  
% 4.59/1.75  tff(f_162, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_2(D, B) & v2_funct_2(E, C)) => v2_funct_2(k1_partfun1(A, B, B, C, D, E), C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_funct_2)).
% 4.59/1.75  tff(f_58, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.59/1.75  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.59/1.75  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.59/1.75  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.59/1.75  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.59/1.75  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.59/1.75  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.59/1.75  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 4.59/1.75  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.59/1.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.59/1.75  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.59/1.75  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.59/1.75  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.59/1.75  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.59/1.75  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.59/1.75  tff(c_78, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.59/1.75  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_116, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.59/1.75  tff(c_125, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_116])).
% 4.59/1.75  tff(c_132, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_125])).
% 4.59/1.75  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.59/1.75  tff(c_62, plain, (v2_funct_2('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_231, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.59/1.75  tff(c_244, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_231])).
% 4.59/1.75  tff(c_403, plain, (![B_111, A_112]: (k2_relat_1(B_111)=A_112 | ~v2_funct_2(B_111, A_112) | ~v5_relat_1(B_111, A_112) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.59/1.75  tff(c_415, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v2_funct_2('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_244, c_403])).
% 4.59/1.75  tff(c_429, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_62, c_415])).
% 4.59/1.75  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_515, plain, (![A_116, B_117, C_118]: (k1_relset_1(A_116, B_117, C_118)=k1_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.59/1.75  tff(c_528, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_515])).
% 4.59/1.75  tff(c_1136, plain, (![B_188, A_189, C_190]: (k1_xboole_0=B_188 | k1_relset_1(A_189, B_188, C_190)=A_189 | ~v1_funct_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.59/1.75  tff(c_1146, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_1136])).
% 4.59/1.75  tff(c_1153, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_528, c_1146])).
% 4.59/1.75  tff(c_1175, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_1153])).
% 4.59/1.75  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_122, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_116])).
% 4.59/1.75  tff(c_129, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_122])).
% 4.59/1.75  tff(c_64, plain, (v2_funct_2('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_243, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_231])).
% 4.59/1.75  tff(c_418, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v2_funct_2('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_243, c_403])).
% 4.59/1.75  tff(c_432, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_64, c_418])).
% 4.59/1.75  tff(c_773, plain, (![B_135, A_136]: (k2_relat_1(k5_relat_1(B_135, A_136))=k2_relat_1(A_136) | ~r1_tarski(k1_relat_1(A_136), k2_relat_1(B_135)) | ~v1_relat_1(B_135) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.59/1.75  tff(c_779, plain, (![A_136]: (k2_relat_1(k5_relat_1('#skF_5', A_136))=k2_relat_1(A_136) | ~r1_tarski(k1_relat_1(A_136), '#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_432, c_773])).
% 4.59/1.75  tff(c_789, plain, (![A_136]: (k2_relat_1(k5_relat_1('#skF_5', A_136))=k2_relat_1(A_136) | ~r1_tarski(k1_relat_1(A_136), '#skF_3') | ~v1_relat_1(A_136))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_779])).
% 4.59/1.75  tff(c_1183, plain, (k2_relat_1(k5_relat_1('#skF_5', '#skF_6'))=k2_relat_1('#skF_6') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1175, c_789])).
% 4.59/1.75  tff(c_1192, plain, (k2_relat_1(k5_relat_1('#skF_5', '#skF_6'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_10, c_429, c_1183])).
% 4.59/1.75  tff(c_314, plain, (![B_107, A_108]: (r1_tarski(k2_relat_1(B_107), A_108) | ~v5_relat_1(B_107, A_108) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.59/1.75  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.59/1.75  tff(c_91, plain, (![B_66, A_67]: (~r1_tarski(B_66, A_67) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.59/1.75  tff(c_95, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_91])).
% 4.59/1.75  tff(c_350, plain, (![B_107]: (v1_xboole_0(k2_relat_1(B_107)) | ~v5_relat_1(B_107, '#skF_1'(k2_relat_1(B_107))) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_314, c_95])).
% 4.59/1.75  tff(c_1227, plain, (v1_xboole_0(k2_relat_1(k5_relat_1('#skF_5', '#skF_6'))) | ~v5_relat_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_1'('#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1192, c_350])).
% 4.59/1.75  tff(c_1242, plain, (v1_xboole_0('#skF_4') | ~v5_relat_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_1'('#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1192, c_1227])).
% 4.59/1.75  tff(c_1243, plain, (~v5_relat_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_1'('#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_1242])).
% 4.59/1.75  tff(c_1246, plain, (~v1_relat_1(k5_relat_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1243])).
% 4.59/1.75  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.75  tff(c_1325, plain, (![B_209, E_207, D_208, A_210, C_212, F_211]: (k1_partfun1(A_210, B_209, C_212, D_208, E_207, F_211)=k5_relat_1(E_207, F_211) | ~m1_subset_1(F_211, k1_zfmisc_1(k2_zfmisc_1(C_212, D_208))) | ~v1_funct_1(F_211) | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))) | ~v1_funct_1(E_207))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.59/1.75  tff(c_1332, plain, (![A_210, B_209, E_207]: (k1_partfun1(A_210, B_209, '#skF_3', '#skF_4', E_207, '#skF_6')=k5_relat_1(E_207, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_207, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))) | ~v1_funct_1(E_207))), inference(resolution, [status(thm)], [c_66, c_1325])).
% 4.59/1.75  tff(c_1539, plain, (![A_234, B_235, E_236]: (k1_partfun1(A_234, B_235, '#skF_3', '#skF_4', E_236, '#skF_6')=k5_relat_1(E_236, '#skF_6') | ~m1_subset_1(E_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_1(E_236))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1332])).
% 4.59/1.75  tff(c_1549, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_1539])).
% 4.59/1.75  tff(c_1557, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1549])).
% 4.59/1.75  tff(c_54, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (m1_subset_1(k1_partfun1(A_36, B_37, C_38, D_39, E_40, F_41), k1_zfmisc_1(k2_zfmisc_1(A_36, D_39))) | ~m1_subset_1(F_41, k1_zfmisc_1(k2_zfmisc_1(C_38, D_39))) | ~v1_funct_1(F_41) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(E_40))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.59/1.75  tff(c_1566, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1557, c_54])).
% 4.59/1.75  tff(c_1570, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1566])).
% 4.59/1.75  tff(c_30, plain, (![C_24, A_22, B_23]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.59/1.75  tff(c_1602, plain, (v1_relat_1(k5_relat_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1570, c_30])).
% 4.59/1.75  tff(c_1632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1246, c_1602])).
% 4.59/1.75  tff(c_1634, plain, (v1_relat_1(k5_relat_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_1243])).
% 4.59/1.75  tff(c_283, plain, (![B_98, A_99]: (v5_relat_1(B_98, A_99) | ~r1_tarski(k2_relat_1(B_98), A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.59/1.75  tff(c_288, plain, (![B_98]: (v5_relat_1(B_98, k2_relat_1(B_98)) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_10, c_283])).
% 4.59/1.75  tff(c_366, plain, (![B_110]: (v2_funct_2(B_110, k2_relat_1(B_110)) | ~v5_relat_1(B_110, k2_relat_1(B_110)) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.59/1.75  tff(c_374, plain, (![B_98]: (v2_funct_2(B_98, k2_relat_1(B_98)) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_288, c_366])).
% 4.59/1.75  tff(c_1230, plain, (v2_funct_2(k5_relat_1('#skF_5', '#skF_6'), '#skF_4') | ~v1_relat_1(k5_relat_1('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1192, c_374])).
% 4.59/1.75  tff(c_1686, plain, (v2_funct_2(k5_relat_1('#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1230])).
% 4.59/1.75  tff(c_1670, plain, (![B_248, F_250, D_247, E_246, A_249, C_251]: (k1_partfun1(A_249, B_248, C_251, D_247, E_246, F_250)=k5_relat_1(E_246, F_250) | ~m1_subset_1(F_250, k1_zfmisc_1(k2_zfmisc_1(C_251, D_247))) | ~v1_funct_1(F_250) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))) | ~v1_funct_1(E_246))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.59/1.75  tff(c_1677, plain, (![A_249, B_248, E_246]: (k1_partfun1(A_249, B_248, '#skF_3', '#skF_4', E_246, '#skF_6')=k5_relat_1(E_246, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))) | ~v1_funct_1(E_246))), inference(resolution, [status(thm)], [c_66, c_1670])).
% 4.59/1.75  tff(c_2168, plain, (![A_275, B_276, E_277]: (k1_partfun1(A_275, B_276, '#skF_3', '#skF_4', E_277, '#skF_6')=k5_relat_1(E_277, '#skF_6') | ~m1_subset_1(E_277, k1_zfmisc_1(k2_zfmisc_1(A_275, B_276))) | ~v1_funct_1(E_277))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1677])).
% 4.59/1.75  tff(c_2184, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_2168])).
% 4.59/1.75  tff(c_2198, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2184])).
% 4.59/1.76  tff(c_60, plain, (~v2_funct_2(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.59/1.76  tff(c_2243, plain, (~v2_funct_2(k5_relat_1('#skF_5', '#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2198, c_60])).
% 4.59/1.76  tff(c_2246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1686, c_2243])).
% 4.59/1.76  tff(c_2247, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1153])).
% 4.59/1.76  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.59/1.76  tff(c_96, plain, (![A_68]: (~r1_tarski(A_68, '#skF_1'(A_68)) | v1_xboole_0(A_68))), inference(resolution, [status(thm)], [c_4, c_91])).
% 4.59/1.76  tff(c_101, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_96])).
% 4.59/1.76  tff(c_2287, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2247, c_101])).
% 4.59/1.76  tff(c_2290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_2287])).
% 4.59/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.76  
% 4.59/1.76  Inference rules
% 4.59/1.76  ----------------------
% 4.59/1.76  #Ref     : 0
% 4.59/1.76  #Sup     : 416
% 4.59/1.76  #Fact    : 0
% 4.59/1.76  #Define  : 0
% 4.59/1.76  #Split   : 16
% 4.59/1.76  #Chain   : 0
% 4.59/1.76  #Close   : 0
% 4.59/1.76  
% 4.59/1.76  Ordering : KBO
% 4.59/1.76  
% 4.59/1.76  Simplification rules
% 4.59/1.76  ----------------------
% 4.59/1.76  #Subsume      : 40
% 4.59/1.76  #Demod        : 467
% 4.59/1.76  #Tautology    : 148
% 4.59/1.76  #SimpNegUnit  : 13
% 4.59/1.76  #BackRed      : 36
% 4.59/1.76  
% 4.59/1.76  #Partial instantiations: 0
% 4.59/1.76  #Strategies tried      : 1
% 4.59/1.76  
% 4.59/1.76  Timing (in seconds)
% 4.59/1.76  ----------------------
% 4.59/1.76  Preprocessing        : 0.35
% 4.59/1.76  Parsing              : 0.18
% 4.59/1.76  CNF conversion       : 0.03
% 4.59/1.76  Main loop            : 0.65
% 4.59/1.76  Inferencing          : 0.23
% 4.59/1.76  Reduction            : 0.24
% 4.59/1.76  Demodulation         : 0.17
% 4.59/1.76  BG Simplification    : 0.03
% 4.59/1.76  Subsumption          : 0.11
% 4.59/1.76  Abstraction          : 0.03
% 4.59/1.76  MUC search           : 0.00
% 4.59/1.76  Cooper               : 0.00
% 4.59/1.76  Total                : 1.04
% 4.59/1.76  Index Insertion      : 0.00
% 4.59/1.76  Index Deletion       : 0.00
% 4.59/1.76  Index Matching       : 0.00
% 4.59/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
