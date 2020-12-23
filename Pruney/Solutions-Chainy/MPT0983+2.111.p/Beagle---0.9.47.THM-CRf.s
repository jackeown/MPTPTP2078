%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:17 EST 2020

% Result     : Theorem 9.00s
% Output     : CNFRefutation 9.18s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 989 expanded)
%              Number of leaves         :   56 ( 351 expanded)
%              Depth                    :   16
%              Number of atoms          :  403 (2585 expanded)
%              Number of equality atoms :   67 ( 277 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_201,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_159,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_157,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_127,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_147,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_181,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v1_xboole_0(k2_zfmisc_1(A_15,B_16))
      | ~ v1_xboole_0(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_167,plain,(
    ! [B_91,A_92] :
      ( v1_xboole_0(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_182,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_82,c_167])).

tff(c_184,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_191,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_184])).

tff(c_78,plain,
    ( ~ v2_funct_2('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_132,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_92,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_90,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_88,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_72,plain,(
    ! [A_59] : k6_relat_1(A_59) = k6_partfun1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_50,plain,(
    ! [A_36] : v2_funct_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_94,plain,(
    ! [A_36] : v2_funct_1(k6_partfun1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50])).

tff(c_1574,plain,(
    ! [F_196,E_193,A_192,D_194,C_191,B_195] :
      ( k1_partfun1(A_192,B_195,C_191,D_194,E_193,F_196) = k5_relat_1(E_193,F_196)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(C_191,D_194)))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_195)))
      | ~ v1_funct_1(E_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1589,plain,(
    ! [A_192,B_195,E_193] :
      ( k1_partfun1(A_192,B_195,'#skF_4','#skF_3',E_193,'#skF_6') = k5_relat_1(E_193,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(A_192,B_195)))
      | ~ v1_funct_1(E_193) ) ),
    inference(resolution,[status(thm)],[c_82,c_1574])).

tff(c_3834,plain,(
    ! [A_321,B_322,E_323] :
      ( k1_partfun1(A_321,B_322,'#skF_4','#skF_3',E_323,'#skF_6') = k5_relat_1(E_323,'#skF_6')
      | ~ m1_subset_1(E_323,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322)))
      | ~ v1_funct_1(E_323) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1589])).

tff(c_3862,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_3834])).

tff(c_3871,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3862])).

tff(c_60,plain,(
    ! [A_44] : m1_subset_1(k6_relat_1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_93,plain,(
    ! [A_44] : m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_60])).

tff(c_80,plain,(
    r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_971,plain,(
    ! [D_155,C_156,A_157,B_158] :
      ( D_155 = C_156
      | ~ r2_relset_1(A_157,B_158,C_156,D_155)
      | ~ m1_subset_1(D_155,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158)))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_977,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_80,c_971])).

tff(c_988,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_977])).

tff(c_1049,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_988])).

tff(c_4213,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3871,c_1049])).

tff(c_66,plain,(
    ! [A_47,F_52,E_51,D_50,C_49,B_48] :
      ( m1_subset_1(k1_partfun1(A_47,B_48,C_49,D_50,E_51,F_52),k1_zfmisc_1(k2_zfmisc_1(A_47,D_50)))
      | ~ m1_subset_1(F_52,k1_zfmisc_1(k2_zfmisc_1(C_49,D_50)))
      | ~ v1_funct_1(F_52)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48)))
      | ~ v1_funct_1(E_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4197,plain,
    ( m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3871,c_66])).

tff(c_4204,plain,(
    m1_subset_1(k5_relat_1('#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_4197])).

tff(c_4524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4213,c_4204])).

tff(c_4525,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_988])).

tff(c_76,plain,(
    ! [D_63,A_60,C_62,E_65,B_61] :
      ( k1_xboole_0 = C_62
      | v2_funct_1(D_63)
      | ~ v2_funct_1(k1_partfun1(A_60,B_61,B_61,C_62,D_63,E_65))
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ v1_funct_2(E_65,B_61,C_62)
      | ~ v1_funct_1(E_65)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(D_63,A_60,B_61)
      | ~ v1_funct_1(D_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6311,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4525,c_76])).

tff(c_6318,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_82,c_94,c_6311])).

tff(c_6319,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_6318])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_247,plain,(
    ! [B_100,A_101] :
      ( ~ r1_xboole_0(B_100,A_101)
      | ~ r1_tarski(B_100,A_101)
      | v1_xboole_0(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_252,plain,(
    ! [A_102] :
      ( ~ r1_tarski(A_102,k1_xboole_0)
      | v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_18,c_247])).

tff(c_257,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_252])).

tff(c_6362,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6319,c_257])).

tff(c_6366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_6362])).

tff(c_6367,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_11109,plain,(
    ! [B_775,A_776] :
      ( ~ r1_xboole_0(B_775,A_776)
      | ~ r1_tarski(B_775,A_776)
      | v1_xboole_0(B_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_11114,plain,(
    ! [A_777] :
      ( ~ r1_tarski(A_777,k1_xboole_0)
      | v1_xboole_0(A_777) ) ),
    inference(resolution,[status(thm)],[c_18,c_11109])).

tff(c_11119,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_11114])).

tff(c_11160,plain,(
    ! [A_784,B_785] :
      ( r2_hidden('#skF_2'(A_784,B_785),A_784)
      | r1_tarski(A_784,B_785) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11170,plain,(
    ! [A_784,B_785] :
      ( ~ v1_xboole_0(A_784)
      | r1_tarski(A_784,B_785) ) ),
    inference(resolution,[status(thm)],[c_11160,c_2])).

tff(c_11171,plain,(
    ! [A_786,B_787] :
      ( ~ v1_xboole_0(A_786)
      | r1_tarski(A_786,B_787) ) ),
    inference(resolution,[status(thm)],[c_11160,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_11238,plain,(
    ! [B_789,A_790] :
      ( B_789 = A_790
      | ~ r1_tarski(B_789,A_790)
      | ~ v1_xboole_0(A_790) ) ),
    inference(resolution,[status(thm)],[c_11171,c_12])).

tff(c_11347,plain,(
    ! [B_794,A_795] :
      ( B_794 = A_795
      | ~ v1_xboole_0(B_794)
      | ~ v1_xboole_0(A_795) ) ),
    inference(resolution,[status(thm)],[c_11170,c_11238])).

tff(c_11366,plain,(
    ! [A_796] :
      ( k1_xboole_0 = A_796
      | ~ v1_xboole_0(A_796) ) ),
    inference(resolution,[status(thm)],[c_11119,c_11347])).

tff(c_11388,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6367,c_11366])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( v1_xboole_0(k2_zfmisc_1(A_17,B_18))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_183,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_167])).

tff(c_6369,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_6377,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_6369])).

tff(c_6368,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_148,plain,(
    ! [A_87,B_88] :
      ( r1_tarski(A_87,B_88)
      | ~ m1_subset_1(A_87,k1_zfmisc_1(B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_159,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_82,c_148])).

tff(c_6408,plain,(
    ! [A_458,B_459] :
      ( r2_hidden('#skF_2'(A_458,B_459),A_458)
      | r1_tarski(A_458,B_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6412,plain,(
    ! [A_458,B_459] :
      ( ~ v1_xboole_0(A_458)
      | r1_tarski(A_458,B_459) ) ),
    inference(resolution,[status(thm)],[c_6408,c_2])).

tff(c_6423,plain,(
    ! [B_464,A_465] :
      ( B_464 = A_465
      | ~ r1_tarski(B_464,A_465)
      | ~ r1_tarski(A_465,B_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6453,plain,(
    ! [B_467,A_468] :
      ( B_467 = A_468
      | ~ r1_tarski(B_467,A_468)
      | ~ v1_xboole_0(A_468) ) ),
    inference(resolution,[status(thm)],[c_6412,c_6423])).

tff(c_6465,plain,
    ( k2_zfmisc_1('#skF_4','#skF_3') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_159,c_6453])).

tff(c_6474,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6368,c_6465])).

tff(c_6479,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6474,c_82])).

tff(c_8171,plain,(
    ! [D_570,C_571,A_572,B_573] :
      ( D_570 = C_571
      | ~ r2_relset_1(A_572,B_573,C_571,D_570)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573)))
      | ~ m1_subset_1(C_571,k1_zfmisc_1(k2_zfmisc_1(A_572,B_573))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8181,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_80,c_8171])).

tff(c_8200,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_8181])).

tff(c_8404,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_8200])).

tff(c_9671,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_8404])).

tff(c_9678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_6479,c_6474,c_9671])).

tff(c_9679,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_8200])).

tff(c_6418,plain,(
    ! [B_462,A_463] :
      ( ~ r1_xboole_0(B_462,A_463)
      | ~ r1_tarski(B_462,A_463)
      | v1_xboole_0(B_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6442,plain,(
    ! [A_466] :
      ( ~ r1_tarski(A_466,k1_xboole_0)
      | v1_xboole_0(A_466) ) ),
    inference(resolution,[status(thm)],[c_18,c_6418])).

tff(c_6452,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_6442])).

tff(c_6530,plain,(
    ! [B_471,A_472] :
      ( B_471 = A_472
      | ~ v1_xboole_0(B_471)
      | ~ v1_xboole_0(A_472) ) ),
    inference(resolution,[status(thm)],[c_6412,c_6453])).

tff(c_6547,plain,(
    ! [A_473] :
      ( k1_xboole_0 = A_473
      | ~ v1_xboole_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_6452,c_6530])).

tff(c_6565,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6367,c_6547])).

tff(c_10691,plain,(
    ! [D_63,A_60,C_62,E_65,B_61] :
      ( C_62 = '#skF_6'
      | v2_funct_1(D_63)
      | ~ v2_funct_1(k1_partfun1(A_60,B_61,B_61,C_62,D_63,E_65))
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ v1_funct_2(E_65,B_61,C_62)
      | ~ v1_funct_1(E_65)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ v1_funct_2(D_63,A_60,B_61)
      | ~ v1_funct_1(D_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6565,c_76])).

tff(c_10949,plain,
    ( '#skF_6' = '#skF_3'
    | v2_funct_1('#skF_5')
    | ~ v2_funct_1(k6_partfun1('#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9679,c_10691])).

tff(c_10956,plain,
    ( '#skF_6' = '#skF_3'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_6479,c_6474,c_94,c_10949])).

tff(c_10957,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_10956])).

tff(c_7077,plain,(
    ! [C_506,B_507,A_508] :
      ( v5_relat_1(C_506,B_507)
      | ~ m1_subset_1(C_506,k1_zfmisc_1(k2_zfmisc_1(A_508,B_507))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7118,plain,(
    ! [C_512] :
      ( v5_relat_1(C_512,'#skF_3')
      | ~ m1_subset_1(C_512,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6474,c_7077])).

tff(c_7126,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_6479,c_7118])).

tff(c_38,plain,(
    ! [A_29,B_30] : v1_relat_1(k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6490,plain,(
    v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6474,c_38])).

tff(c_48,plain,(
    ! [A_36] : v1_relat_1(k6_relat_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_95,plain,(
    ! [A_36] : v1_relat_1(k6_partfun1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_48])).

tff(c_46,plain,(
    ! [A_35] : k2_relat_1(k6_relat_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_96,plain,(
    ! [A_35] : k2_relat_1(k6_partfun1(A_35)) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46])).

tff(c_140,plain,(
    ! [A_83] :
      ( ~ v1_xboole_0(k2_relat_1(A_83))
      | ~ v1_relat_1(A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_143,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(A_35)
      | ~ v1_relat_1(k6_partfun1(A_35))
      | v1_xboole_0(k6_partfun1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_140])).

tff(c_145,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(A_35)
      | v1_xboole_0(k6_partfun1(A_35)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_143])).

tff(c_6566,plain,(
    ! [A_35] :
      ( k6_partfun1(A_35) = k1_xboole_0
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_145,c_6547])).

tff(c_6613,plain,(
    ! [A_478] :
      ( k6_partfun1(A_478) = '#skF_6'
      | ~ v1_xboole_0(A_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6565,c_6566])).

tff(c_6626,plain,(
    k6_partfun1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6367,c_6613])).

tff(c_6642,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_6626,c_96])).

tff(c_6797,plain,(
    ! [B_489,A_490] :
      ( r1_tarski(k2_relat_1(B_489),A_490)
      | ~ v5_relat_1(B_489,A_490)
      | ~ v1_relat_1(B_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6815,plain,(
    ! [A_490] :
      ( r1_tarski('#skF_6',A_490)
      | ~ v5_relat_1('#skF_6',A_490)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6642,c_6797])).

tff(c_6825,plain,(
    ! [A_490] :
      ( r1_tarski('#skF_6',A_490)
      | ~ v5_relat_1('#skF_6',A_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6490,c_6815])).

tff(c_7131,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_7126,c_6825])).

tff(c_7146,plain,
    ( '#skF_6' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_7131,c_12])).

tff(c_7149,plain,(
    ~ r1_tarski('#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7146])).

tff(c_10989,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10957,c_7149])).

tff(c_11012,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10989])).

tff(c_11013,plain,(
    '#skF_6' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7146])).

tff(c_11045,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11013,c_6367])).

tff(c_11051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6377,c_11045])).

tff(c_11052,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_11387,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_11052,c_11366])).

tff(c_11403,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11388,c_11387])).

tff(c_11413,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11403,c_132])).

tff(c_11389,plain,(
    ! [A_35] :
      ( k6_partfun1(A_35) = k1_xboole_0
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_145,c_11366])).

tff(c_11482,plain,(
    ! [A_801] :
      ( k6_partfun1(A_801) = '#skF_6'
      | ~ v1_xboole_0(A_801) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11388,c_11389])).

tff(c_11495,plain,(
    k6_partfun1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6367,c_11482])).

tff(c_11518,plain,(
    v2_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_11495,c_94])).

tff(c_11525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11413,c_11518])).

tff(c_11526,plain,(
    ~ v2_funct_2('#skF_6','#skF_3') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_11586,plain,(
    ! [B_821,A_822] :
      ( v1_relat_1(B_821)
      | ~ m1_subset_1(B_821,k1_zfmisc_1(A_822))
      | ~ v1_relat_1(A_822) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11595,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_82,c_11586])).

tff(c_11605,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11595])).

tff(c_11980,plain,(
    ! [C_850,B_851,A_852] :
      ( v5_relat_1(C_850,B_851)
      | ~ m1_subset_1(C_850,k1_zfmisc_1(k2_zfmisc_1(A_852,B_851))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11999,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_11980])).

tff(c_36,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_11598,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_88,c_11586])).

tff(c_11608,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11598])).

tff(c_12566,plain,(
    ! [D_891,C_892,A_893,B_894] :
      ( D_891 = C_892
      | ~ r2_relset_1(A_893,B_894,C_892,D_891)
      | ~ m1_subset_1(D_891,k1_zfmisc_1(k2_zfmisc_1(A_893,B_894)))
      | ~ m1_subset_1(C_892,k1_zfmisc_1(k2_zfmisc_1(A_893,B_894))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_12576,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k6_partfun1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_80,c_12566])).

tff(c_12595,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3')
    | ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_12576])).

tff(c_12795,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_12595])).

tff(c_15701,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_12795])).

tff(c_15708,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_15701])).

tff(c_15709,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_12595])).

tff(c_16055,plain,(
    ! [D_1089,F_1091,B_1090,C_1086,A_1087,E_1088] :
      ( k1_partfun1(A_1087,B_1090,C_1086,D_1089,E_1088,F_1091) = k5_relat_1(E_1088,F_1091)
      | ~ m1_subset_1(F_1091,k1_zfmisc_1(k2_zfmisc_1(C_1086,D_1089)))
      | ~ v1_funct_1(F_1091)
      | ~ m1_subset_1(E_1088,k1_zfmisc_1(k2_zfmisc_1(A_1087,B_1090)))
      | ~ v1_funct_1(E_1088) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_16070,plain,(
    ! [A_1087,B_1090,E_1088] :
      ( k1_partfun1(A_1087,B_1090,'#skF_4','#skF_3',E_1088,'#skF_6') = k5_relat_1(E_1088,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_1088,k1_zfmisc_1(k2_zfmisc_1(A_1087,B_1090)))
      | ~ v1_funct_1(E_1088) ) ),
    inference(resolution,[status(thm)],[c_82,c_16055])).

tff(c_17147,plain,(
    ! [A_1166,B_1167,E_1168] :
      ( k1_partfun1(A_1166,B_1167,'#skF_4','#skF_3',E_1168,'#skF_6') = k5_relat_1(E_1168,'#skF_6')
      | ~ m1_subset_1(E_1168,k1_zfmisc_1(k2_zfmisc_1(A_1166,B_1167)))
      | ~ v1_funct_1(E_1168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_16070])).

tff(c_17175,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_3','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_17147])).

tff(c_17184,plain,(
    k5_relat_1('#skF_5','#skF_6') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_15709,c_17175])).

tff(c_42,plain,(
    ! [A_32,B_34] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_32,B_34)),k2_relat_1(B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_17188,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_3')),k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_17184,c_42])).

tff(c_17192,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11608,c_11605,c_96,c_17188])).

tff(c_17206,plain,
    ( k2_relat_1('#skF_6') = '#skF_3'
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_17192,c_12])).

tff(c_17687,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_17206])).

tff(c_17690,plain,
    ( ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_17687])).

tff(c_17697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11605,c_11999,c_17690])).

tff(c_17698,plain,(
    k2_relat_1('#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_17206])).

tff(c_12176,plain,(
    ! [B_864,A_865] :
      ( v5_relat_1(B_864,A_865)
      | ~ r1_tarski(k2_relat_1(B_864),A_865)
      | ~ v1_relat_1(B_864) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12200,plain,(
    ! [B_864] :
      ( v5_relat_1(B_864,k2_relat_1(B_864))
      | ~ v1_relat_1(B_864) ) ),
    inference(resolution,[status(thm)],[c_16,c_12176])).

tff(c_12249,plain,(
    ! [B_870] :
      ( v2_funct_2(B_870,k2_relat_1(B_870))
      | ~ v5_relat_1(B_870,k2_relat_1(B_870))
      | ~ v1_relat_1(B_870) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_12259,plain,(
    ! [B_864] :
      ( v2_funct_2(B_864,k2_relat_1(B_864))
      | ~ v1_relat_1(B_864) ) ),
    inference(resolution,[status(thm)],[c_12200,c_12249])).

tff(c_17713,plain,
    ( v2_funct_2('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_17698,c_12259])).

tff(c_17734,plain,(
    v2_funct_2('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11605,c_17713])).

tff(c_17736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11526,c_17734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.00/3.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.11/3.52  
% 9.11/3.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.11/3.53  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 9.11/3.53  
% 9.11/3.53  %Foreground sorts:
% 9.11/3.53  
% 9.11/3.53  
% 9.11/3.53  %Background operators:
% 9.11/3.53  
% 9.11/3.53  
% 9.11/3.53  %Foreground operators:
% 9.11/3.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.11/3.53  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.11/3.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.11/3.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.11/3.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.11/3.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.11/3.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.11/3.53  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.11/3.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.11/3.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.11/3.53  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.11/3.53  tff('#skF_5', type, '#skF_5': $i).
% 9.11/3.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.11/3.53  tff('#skF_6', type, '#skF_6': $i).
% 9.11/3.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.11/3.53  tff('#skF_3', type, '#skF_3': $i).
% 9.11/3.53  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 9.11/3.53  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.11/3.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.11/3.53  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.11/3.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.11/3.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.11/3.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.11/3.53  tff('#skF_4', type, '#skF_4': $i).
% 9.11/3.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.11/3.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.11/3.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.11/3.53  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.11/3.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.11/3.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.11/3.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.11/3.53  
% 9.18/3.55  tff(f_58, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 9.18/3.55  tff(f_201, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 9.18/3.55  tff(f_69, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 9.18/3.55  tff(f_159, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.18/3.55  tff(f_111, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.18/3.55  tff(f_157, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.18/3.55  tff(f_127, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 9.18/3.55  tff(f_125, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.18/3.55  tff(f_147, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.18/3.55  tff(f_181, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 9.18/3.55  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.18/3.55  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.18/3.55  tff(f_54, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 9.18/3.55  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.18/3.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.18/3.55  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 9.18/3.55  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.18/3.55  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.18/3.55  tff(f_88, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.18/3.55  tff(f_107, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.18/3.55  tff(f_96, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 9.18/3.55  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 9.18/3.55  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.18/3.55  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 9.18/3.55  tff(f_135, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 9.18/3.55  tff(c_22, plain, (![A_15, B_16]: (v1_xboole_0(k2_zfmisc_1(A_15, B_16)) | ~v1_xboole_0(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.18/3.55  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_167, plain, (![B_91, A_92]: (v1_xboole_0(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.18/3.55  tff(c_182, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_82, c_167])).
% 9.18/3.55  tff(c_184, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_182])).
% 9.18/3.55  tff(c_191, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_184])).
% 9.18/3.55  tff(c_78, plain, (~v2_funct_2('#skF_6', '#skF_3') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_132, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 9.18/3.55  tff(c_92, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_90, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_88, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_72, plain, (![A_59]: (k6_relat_1(A_59)=k6_partfun1(A_59))), inference(cnfTransformation, [status(thm)], [f_159])).
% 9.18/3.55  tff(c_50, plain, (![A_36]: (v2_funct_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.18/3.55  tff(c_94, plain, (![A_36]: (v2_funct_1(k6_partfun1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50])).
% 9.18/3.55  tff(c_1574, plain, (![F_196, E_193, A_192, D_194, C_191, B_195]: (k1_partfun1(A_192, B_195, C_191, D_194, E_193, F_196)=k5_relat_1(E_193, F_196) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(C_191, D_194))) | ~v1_funct_1(F_196) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_195))) | ~v1_funct_1(E_193))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.18/3.55  tff(c_1589, plain, (![A_192, B_195, E_193]: (k1_partfun1(A_192, B_195, '#skF_4', '#skF_3', E_193, '#skF_6')=k5_relat_1(E_193, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(A_192, B_195))) | ~v1_funct_1(E_193))), inference(resolution, [status(thm)], [c_82, c_1574])).
% 9.18/3.55  tff(c_3834, plain, (![A_321, B_322, E_323]: (k1_partfun1(A_321, B_322, '#skF_4', '#skF_3', E_323, '#skF_6')=k5_relat_1(E_323, '#skF_6') | ~m1_subset_1(E_323, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))) | ~v1_funct_1(E_323))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1589])).
% 9.18/3.55  tff(c_3862, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_3834])).
% 9.18/3.55  tff(c_3871, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3862])).
% 9.18/3.55  tff(c_60, plain, (![A_44]: (m1_subset_1(k6_relat_1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.18/3.55  tff(c_93, plain, (![A_44]: (m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_60])).
% 9.18/3.55  tff(c_80, plain, (r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 9.18/3.55  tff(c_971, plain, (![D_155, C_156, A_157, B_158]: (D_155=C_156 | ~r2_relset_1(A_157, B_158, C_156, D_155) | ~m1_subset_1(D_155, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.18/3.55  tff(c_977, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_80, c_971])).
% 9.18/3.55  tff(c_988, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_977])).
% 9.18/3.55  tff(c_1049, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_988])).
% 9.18/3.55  tff(c_4213, plain, (~m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_3871, c_1049])).
% 9.18/3.55  tff(c_66, plain, (![A_47, F_52, E_51, D_50, C_49, B_48]: (m1_subset_1(k1_partfun1(A_47, B_48, C_49, D_50, E_51, F_52), k1_zfmisc_1(k2_zfmisc_1(A_47, D_50))) | ~m1_subset_1(F_52, k1_zfmisc_1(k2_zfmisc_1(C_49, D_50))) | ~v1_funct_1(F_52) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))) | ~v1_funct_1(E_51))), inference(cnfTransformation, [status(thm)], [f_147])).
% 9.18/3.55  tff(c_4197, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3871, c_66])).
% 9.18/3.55  tff(c_4204, plain, (m1_subset_1(k5_relat_1('#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_4197])).
% 9.18/3.55  tff(c_4524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4213, c_4204])).
% 9.18/3.55  tff(c_4525, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_988])).
% 9.18/3.55  tff(c_76, plain, (![D_63, A_60, C_62, E_65, B_61]: (k1_xboole_0=C_62 | v2_funct_1(D_63) | ~v2_funct_1(k1_partfun1(A_60, B_61, B_61, C_62, D_63, E_65)) | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~v1_funct_2(E_65, B_61, C_62) | ~v1_funct_1(E_65) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(D_63, A_60, B_61) | ~v1_funct_1(D_63))), inference(cnfTransformation, [status(thm)], [f_181])).
% 9.18/3.55  tff(c_6311, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4525, c_76])).
% 9.18/3.55  tff(c_6318, plain, (k1_xboole_0='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_82, c_94, c_6311])).
% 9.18/3.55  tff(c_6319, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_132, c_6318])).
% 9.18/3.55  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.18/3.55  tff(c_18, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.18/3.55  tff(c_247, plain, (![B_100, A_101]: (~r1_xboole_0(B_100, A_101) | ~r1_tarski(B_100, A_101) | v1_xboole_0(B_100))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.18/3.55  tff(c_252, plain, (![A_102]: (~r1_tarski(A_102, k1_xboole_0) | v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_18, c_247])).
% 9.18/3.55  tff(c_257, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_252])).
% 9.18/3.55  tff(c_6362, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6319, c_257])).
% 9.18/3.55  tff(c_6366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_6362])).
% 9.18/3.55  tff(c_6367, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_182])).
% 9.18/3.55  tff(c_11109, plain, (![B_775, A_776]: (~r1_xboole_0(B_775, A_776) | ~r1_tarski(B_775, A_776) | v1_xboole_0(B_775))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.18/3.55  tff(c_11114, plain, (![A_777]: (~r1_tarski(A_777, k1_xboole_0) | v1_xboole_0(A_777))), inference(resolution, [status(thm)], [c_18, c_11109])).
% 9.18/3.55  tff(c_11119, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_11114])).
% 9.18/3.55  tff(c_11160, plain, (![A_784, B_785]: (r2_hidden('#skF_2'(A_784, B_785), A_784) | r1_tarski(A_784, B_785))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.18/3.55  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.18/3.55  tff(c_11170, plain, (![A_784, B_785]: (~v1_xboole_0(A_784) | r1_tarski(A_784, B_785))), inference(resolution, [status(thm)], [c_11160, c_2])).
% 9.18/3.55  tff(c_11171, plain, (![A_786, B_787]: (~v1_xboole_0(A_786) | r1_tarski(A_786, B_787))), inference(resolution, [status(thm)], [c_11160, c_2])).
% 9.18/3.55  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.18/3.55  tff(c_11238, plain, (![B_789, A_790]: (B_789=A_790 | ~r1_tarski(B_789, A_790) | ~v1_xboole_0(A_790))), inference(resolution, [status(thm)], [c_11171, c_12])).
% 9.18/3.55  tff(c_11347, plain, (![B_794, A_795]: (B_794=A_795 | ~v1_xboole_0(B_794) | ~v1_xboole_0(A_795))), inference(resolution, [status(thm)], [c_11170, c_11238])).
% 9.18/3.55  tff(c_11366, plain, (![A_796]: (k1_xboole_0=A_796 | ~v1_xboole_0(A_796))), inference(resolution, [status(thm)], [c_11119, c_11347])).
% 9.18/3.55  tff(c_11388, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6367, c_11366])).
% 9.18/3.55  tff(c_24, plain, (![A_17, B_18]: (v1_xboole_0(k2_zfmisc_1(A_17, B_18)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.18/3.55  tff(c_183, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_167])).
% 9.18/3.55  tff(c_6369, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_183])).
% 9.18/3.55  tff(c_6377, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_24, c_6369])).
% 9.18/3.55  tff(c_6368, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_182])).
% 9.18/3.55  tff(c_148, plain, (![A_87, B_88]: (r1_tarski(A_87, B_88) | ~m1_subset_1(A_87, k1_zfmisc_1(B_88)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.18/3.55  tff(c_159, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_82, c_148])).
% 9.18/3.55  tff(c_6408, plain, (![A_458, B_459]: (r2_hidden('#skF_2'(A_458, B_459), A_458) | r1_tarski(A_458, B_459))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.18/3.55  tff(c_6412, plain, (![A_458, B_459]: (~v1_xboole_0(A_458) | r1_tarski(A_458, B_459))), inference(resolution, [status(thm)], [c_6408, c_2])).
% 9.18/3.55  tff(c_6423, plain, (![B_464, A_465]: (B_464=A_465 | ~r1_tarski(B_464, A_465) | ~r1_tarski(A_465, B_464))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.18/3.55  tff(c_6453, plain, (![B_467, A_468]: (B_467=A_468 | ~r1_tarski(B_467, A_468) | ~v1_xboole_0(A_468))), inference(resolution, [status(thm)], [c_6412, c_6423])).
% 9.18/3.55  tff(c_6465, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_159, c_6453])).
% 9.18/3.55  tff(c_6474, plain, (k2_zfmisc_1('#skF_4', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6368, c_6465])).
% 9.18/3.55  tff(c_6479, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6474, c_82])).
% 9.18/3.55  tff(c_8171, plain, (![D_570, C_571, A_572, B_573]: (D_570=C_571 | ~r2_relset_1(A_572, B_573, C_571, D_570) | ~m1_subset_1(D_570, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))) | ~m1_subset_1(C_571, k1_zfmisc_1(k2_zfmisc_1(A_572, B_573))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.18/3.56  tff(c_8181, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_80, c_8171])).
% 9.18/3.56  tff(c_8200, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_8181])).
% 9.18/3.56  tff(c_8404, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_8200])).
% 9.18/3.56  tff(c_9671, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_8404])).
% 9.18/3.56  tff(c_9678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_6479, c_6474, c_9671])).
% 9.18/3.56  tff(c_9679, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_8200])).
% 9.18/3.56  tff(c_6418, plain, (![B_462, A_463]: (~r1_xboole_0(B_462, A_463) | ~r1_tarski(B_462, A_463) | v1_xboole_0(B_462))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.18/3.56  tff(c_6442, plain, (![A_466]: (~r1_tarski(A_466, k1_xboole_0) | v1_xboole_0(A_466))), inference(resolution, [status(thm)], [c_18, c_6418])).
% 9.18/3.56  tff(c_6452, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_6442])).
% 9.18/3.56  tff(c_6530, plain, (![B_471, A_472]: (B_471=A_472 | ~v1_xboole_0(B_471) | ~v1_xboole_0(A_472))), inference(resolution, [status(thm)], [c_6412, c_6453])).
% 9.18/3.56  tff(c_6547, plain, (![A_473]: (k1_xboole_0=A_473 | ~v1_xboole_0(A_473))), inference(resolution, [status(thm)], [c_6452, c_6530])).
% 9.18/3.56  tff(c_6565, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6367, c_6547])).
% 9.18/3.56  tff(c_10691, plain, (![D_63, A_60, C_62, E_65, B_61]: (C_62='#skF_6' | v2_funct_1(D_63) | ~v2_funct_1(k1_partfun1(A_60, B_61, B_61, C_62, D_63, E_65)) | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~v1_funct_2(E_65, B_61, C_62) | ~v1_funct_1(E_65) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~v1_funct_2(D_63, A_60, B_61) | ~v1_funct_1(D_63))), inference(demodulation, [status(thm), theory('equality')], [c_6565, c_76])).
% 9.18/3.56  tff(c_10949, plain, ('#skF_6'='#skF_3' | v2_funct_1('#skF_5') | ~v2_funct_1(k6_partfun1('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9679, c_10691])).
% 9.18/3.56  tff(c_10956, plain, ('#skF_6'='#skF_3' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_6479, c_6474, c_94, c_10949])).
% 9.18/3.56  tff(c_10957, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_132, c_10956])).
% 9.18/3.56  tff(c_7077, plain, (![C_506, B_507, A_508]: (v5_relat_1(C_506, B_507) | ~m1_subset_1(C_506, k1_zfmisc_1(k2_zfmisc_1(A_508, B_507))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.18/3.56  tff(c_7118, plain, (![C_512]: (v5_relat_1(C_512, '#skF_3') | ~m1_subset_1(C_512, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_6474, c_7077])).
% 9.18/3.56  tff(c_7126, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_6479, c_7118])).
% 9.18/3.56  tff(c_38, plain, (![A_29, B_30]: (v1_relat_1(k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.18/3.56  tff(c_6490, plain, (v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6474, c_38])).
% 9.18/3.56  tff(c_48, plain, (![A_36]: (v1_relat_1(k6_relat_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.18/3.56  tff(c_95, plain, (![A_36]: (v1_relat_1(k6_partfun1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_48])).
% 9.18/3.56  tff(c_46, plain, (![A_35]: (k2_relat_1(k6_relat_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_107])).
% 9.18/3.56  tff(c_96, plain, (![A_35]: (k2_relat_1(k6_partfun1(A_35))=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_46])).
% 9.18/3.56  tff(c_140, plain, (![A_83]: (~v1_xboole_0(k2_relat_1(A_83)) | ~v1_relat_1(A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_96])).
% 9.18/3.56  tff(c_143, plain, (![A_35]: (~v1_xboole_0(A_35) | ~v1_relat_1(k6_partfun1(A_35)) | v1_xboole_0(k6_partfun1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_140])).
% 9.18/3.56  tff(c_145, plain, (![A_35]: (~v1_xboole_0(A_35) | v1_xboole_0(k6_partfun1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_143])).
% 9.18/3.56  tff(c_6566, plain, (![A_35]: (k6_partfun1(A_35)=k1_xboole_0 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_145, c_6547])).
% 9.18/3.56  tff(c_6613, plain, (![A_478]: (k6_partfun1(A_478)='#skF_6' | ~v1_xboole_0(A_478))), inference(demodulation, [status(thm), theory('equality')], [c_6565, c_6566])).
% 9.18/3.56  tff(c_6626, plain, (k6_partfun1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_6367, c_6613])).
% 9.18/3.56  tff(c_6642, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_6626, c_96])).
% 9.18/3.56  tff(c_6797, plain, (![B_489, A_490]: (r1_tarski(k2_relat_1(B_489), A_490) | ~v5_relat_1(B_489, A_490) | ~v1_relat_1(B_489))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.18/3.56  tff(c_6815, plain, (![A_490]: (r1_tarski('#skF_6', A_490) | ~v5_relat_1('#skF_6', A_490) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6642, c_6797])).
% 9.18/3.56  tff(c_6825, plain, (![A_490]: (r1_tarski('#skF_6', A_490) | ~v5_relat_1('#skF_6', A_490))), inference(demodulation, [status(thm), theory('equality')], [c_6490, c_6815])).
% 9.18/3.56  tff(c_7131, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_7126, c_6825])).
% 9.18/3.56  tff(c_7146, plain, ('#skF_6'='#skF_3' | ~r1_tarski('#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_7131, c_12])).
% 9.18/3.56  tff(c_7149, plain, (~r1_tarski('#skF_3', '#skF_6')), inference(splitLeft, [status(thm)], [c_7146])).
% 9.18/3.56  tff(c_10989, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10957, c_7149])).
% 9.18/3.56  tff(c_11012, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_10989])).
% 9.18/3.56  tff(c_11013, plain, ('#skF_6'='#skF_3'), inference(splitRight, [status(thm)], [c_7146])).
% 9.18/3.56  tff(c_11045, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11013, c_6367])).
% 9.18/3.56  tff(c_11051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6377, c_11045])).
% 9.18/3.56  tff(c_11052, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_183])).
% 9.18/3.56  tff(c_11387, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_11052, c_11366])).
% 9.18/3.56  tff(c_11403, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11388, c_11387])).
% 9.18/3.56  tff(c_11413, plain, (~v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_11403, c_132])).
% 9.18/3.56  tff(c_11389, plain, (![A_35]: (k6_partfun1(A_35)=k1_xboole_0 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_145, c_11366])).
% 9.18/3.56  tff(c_11482, plain, (![A_801]: (k6_partfun1(A_801)='#skF_6' | ~v1_xboole_0(A_801))), inference(demodulation, [status(thm), theory('equality')], [c_11388, c_11389])).
% 9.18/3.56  tff(c_11495, plain, (k6_partfun1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_6367, c_11482])).
% 9.18/3.56  tff(c_11518, plain, (v2_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_11495, c_94])).
% 9.18/3.56  tff(c_11525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11413, c_11518])).
% 9.18/3.56  tff(c_11526, plain, (~v2_funct_2('#skF_6', '#skF_3')), inference(splitRight, [status(thm)], [c_78])).
% 9.18/3.56  tff(c_11586, plain, (![B_821, A_822]: (v1_relat_1(B_821) | ~m1_subset_1(B_821, k1_zfmisc_1(A_822)) | ~v1_relat_1(A_822))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.18/3.56  tff(c_11595, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_82, c_11586])).
% 9.18/3.56  tff(c_11605, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_11595])).
% 9.18/3.56  tff(c_11980, plain, (![C_850, B_851, A_852]: (v5_relat_1(C_850, B_851) | ~m1_subset_1(C_850, k1_zfmisc_1(k2_zfmisc_1(A_852, B_851))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.18/3.56  tff(c_11999, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_82, c_11980])).
% 9.18/3.56  tff(c_36, plain, (![B_28, A_27]: (r1_tarski(k2_relat_1(B_28), A_27) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.18/3.56  tff(c_11598, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_88, c_11586])).
% 9.18/3.56  tff(c_11608, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_11598])).
% 9.18/3.56  tff(c_12566, plain, (![D_891, C_892, A_893, B_894]: (D_891=C_892 | ~r2_relset_1(A_893, B_894, C_892, D_891) | ~m1_subset_1(D_891, k1_zfmisc_1(k2_zfmisc_1(A_893, B_894))) | ~m1_subset_1(C_892, k1_zfmisc_1(k2_zfmisc_1(A_893, B_894))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.18/3.56  tff(c_12576, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k6_partfun1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(resolution, [status(thm)], [c_80, c_12566])).
% 9.18/3.56  tff(c_12595, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3') | ~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_12576])).
% 9.18/3.56  tff(c_12795, plain, (~m1_subset_1(k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(splitLeft, [status(thm)], [c_12595])).
% 9.18/3.56  tff(c_15701, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_12795])).
% 9.18/3.56  tff(c_15708, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_15701])).
% 9.18/3.56  tff(c_15709, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_12595])).
% 9.18/3.56  tff(c_16055, plain, (![D_1089, F_1091, B_1090, C_1086, A_1087, E_1088]: (k1_partfun1(A_1087, B_1090, C_1086, D_1089, E_1088, F_1091)=k5_relat_1(E_1088, F_1091) | ~m1_subset_1(F_1091, k1_zfmisc_1(k2_zfmisc_1(C_1086, D_1089))) | ~v1_funct_1(F_1091) | ~m1_subset_1(E_1088, k1_zfmisc_1(k2_zfmisc_1(A_1087, B_1090))) | ~v1_funct_1(E_1088))), inference(cnfTransformation, [status(thm)], [f_157])).
% 9.18/3.56  tff(c_16070, plain, (![A_1087, B_1090, E_1088]: (k1_partfun1(A_1087, B_1090, '#skF_4', '#skF_3', E_1088, '#skF_6')=k5_relat_1(E_1088, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_1088, k1_zfmisc_1(k2_zfmisc_1(A_1087, B_1090))) | ~v1_funct_1(E_1088))), inference(resolution, [status(thm)], [c_82, c_16055])).
% 9.18/3.56  tff(c_17147, plain, (![A_1166, B_1167, E_1168]: (k1_partfun1(A_1166, B_1167, '#skF_4', '#skF_3', E_1168, '#skF_6')=k5_relat_1(E_1168, '#skF_6') | ~m1_subset_1(E_1168, k1_zfmisc_1(k2_zfmisc_1(A_1166, B_1167))) | ~v1_funct_1(E_1168))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_16070])).
% 9.18/3.56  tff(c_17175, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_3', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_88, c_17147])).
% 9.18/3.56  tff(c_17184, plain, (k5_relat_1('#skF_5', '#skF_6')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_15709, c_17175])).
% 9.18/3.56  tff(c_42, plain, (![A_32, B_34]: (r1_tarski(k2_relat_1(k5_relat_1(A_32, B_34)), k2_relat_1(B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.18/3.56  tff(c_17188, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_3')), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_17184, c_42])).
% 9.18/3.56  tff(c_17192, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11608, c_11605, c_96, c_17188])).
% 9.18/3.56  tff(c_17206, plain, (k2_relat_1('#skF_6')='#skF_3' | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_17192, c_12])).
% 9.18/3.56  tff(c_17687, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_17206])).
% 9.18/3.56  tff(c_17690, plain, (~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_17687])).
% 9.18/3.56  tff(c_17697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11605, c_11999, c_17690])).
% 9.18/3.56  tff(c_17698, plain, (k2_relat_1('#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_17206])).
% 9.18/3.56  tff(c_12176, plain, (![B_864, A_865]: (v5_relat_1(B_864, A_865) | ~r1_tarski(k2_relat_1(B_864), A_865) | ~v1_relat_1(B_864))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.18/3.56  tff(c_12200, plain, (![B_864]: (v5_relat_1(B_864, k2_relat_1(B_864)) | ~v1_relat_1(B_864))), inference(resolution, [status(thm)], [c_16, c_12176])).
% 9.18/3.56  tff(c_12249, plain, (![B_870]: (v2_funct_2(B_870, k2_relat_1(B_870)) | ~v5_relat_1(B_870, k2_relat_1(B_870)) | ~v1_relat_1(B_870))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.18/3.56  tff(c_12259, plain, (![B_864]: (v2_funct_2(B_864, k2_relat_1(B_864)) | ~v1_relat_1(B_864))), inference(resolution, [status(thm)], [c_12200, c_12249])).
% 9.18/3.56  tff(c_17713, plain, (v2_funct_2('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_17698, c_12259])).
% 9.18/3.56  tff(c_17734, plain, (v2_funct_2('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11605, c_17713])).
% 9.18/3.56  tff(c_17736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11526, c_17734])).
% 9.18/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.18/3.56  
% 9.18/3.56  Inference rules
% 9.18/3.56  ----------------------
% 9.18/3.56  #Ref     : 0
% 9.18/3.56  #Sup     : 4052
% 9.18/3.56  #Fact    : 0
% 9.18/3.56  #Define  : 0
% 9.18/3.56  #Split   : 28
% 9.18/3.56  #Chain   : 0
% 9.18/3.56  #Close   : 0
% 9.18/3.56  
% 9.18/3.56  Ordering : KBO
% 9.18/3.56  
% 9.18/3.56  Simplification rules
% 9.18/3.56  ----------------------
% 9.18/3.56  #Subsume      : 723
% 9.18/3.56  #Demod        : 3133
% 9.18/3.56  #Tautology    : 1899
% 9.18/3.56  #SimpNegUnit  : 34
% 9.18/3.56  #BackRed      : 193
% 9.18/3.56  
% 9.18/3.56  #Partial instantiations: 0
% 9.18/3.56  #Strategies tried      : 1
% 9.18/3.56  
% 9.18/3.56  Timing (in seconds)
% 9.18/3.56  ----------------------
% 9.18/3.56  Preprocessing        : 0.37
% 9.18/3.56  Parsing              : 0.19
% 9.18/3.56  CNF conversion       : 0.03
% 9.18/3.56  Main loop            : 2.39
% 9.18/3.56  Inferencing          : 0.75
% 9.18/3.56  Reduction            : 0.86
% 9.18/3.56  Demodulation         : 0.64
% 9.18/3.56  BG Simplification    : 0.07
% 9.18/3.56  Subsumption          : 0.51
% 9.18/3.56  Abstraction          : 0.09
% 9.18/3.56  MUC search           : 0.00
% 9.18/3.56  Cooper               : 0.00
% 9.18/3.56  Total                : 2.82
% 9.18/3.56  Index Insertion      : 0.00
% 9.18/3.56  Index Deletion       : 0.00
% 9.18/3.56  Index Matching       : 0.00
% 9.18/3.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
