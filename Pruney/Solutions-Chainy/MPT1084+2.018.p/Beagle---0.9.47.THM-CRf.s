%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:22 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 456 expanded)
%              Number of leaves         :   35 ( 169 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 (1201 expanded)
%              Number of equality atoms :   36 ( 197 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_114,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_6,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_64,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_67])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_72,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_72])).

tff(c_84,plain,(
    ! [B_60,A_61] :
      ( k1_relat_1(B_60) = A_61
      | ~ v1_partfun1(B_60,A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_87,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_84])).

tff(c_90,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_87])).

tff(c_91,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_99,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_partfun1(C_66,A_67)
      | ~ v1_funct_2(C_66,A_67,B_68)
      | ~ v1_funct_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | v1_xboole_0(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_102,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_105,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_102])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_91,c_105])).

tff(c_108,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_36,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_10,plain,(
    ! [B_9] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_9),B_9),k1_relat_1(B_9))
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_121,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_71),B_71),k1_relat_1(B_71))
      | k6_partfun1(k1_relat_1(B_71)) = B_71
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_127,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),k1_relat_1('#skF_4'))
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_121])).

tff(c_133,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_46,c_108,c_108,c_127])).

tff(c_136,plain,(
    k6_partfun1('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_38,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4',k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_137,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_38])).

tff(c_30,plain,(
    ! [D_30,A_22,B_23,C_24] :
      ( k1_funct_1(D_30,'#skF_2'(A_22,B_23,C_24,D_30)) != k1_funct_1(C_24,'#skF_2'(A_22,B_23,C_24,D_30))
      | r2_funct_2(A_22,B_23,C_24,D_30)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(D_30,A_22,B_23)
      | ~ v1_funct_1(D_30)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_245,plain,(
    ! [A_104,B_105,C_106] :
      ( r2_funct_2(A_104,B_105,C_106,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(C_106,A_104,B_105)
      | ~ v1_funct_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(C_106,A_104,B_105)
      | ~ v1_funct_1(C_106) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_30])).

tff(c_247,plain,
    ( r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_245])).

tff(c_250,plain,(
    r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_250])).

tff(c_254,plain,(
    k6_partfun1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_8,plain,(
    ! [B_9] :
      ( k1_funct_1(B_9,'#skF_1'(k1_relat_1(B_9),B_9)) != '#skF_1'(k1_relat_1(B_9),B_9)
      | k6_relat_1(k1_relat_1(B_9)) = B_9
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_290,plain,(
    ! [B_111] :
      ( k1_funct_1(B_111,'#skF_1'(k1_relat_1(B_111),B_111)) != '#skF_1'(k1_relat_1(B_111),B_111)
      | k6_partfun1(k1_relat_1(B_111)) = B_111
      | ~ v1_funct_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_293,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'(k1_relat_1('#skF_4'),'#skF_4')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_290])).

tff(c_295,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'('#skF_3','#skF_4')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_46,c_108,c_108,c_293])).

tff(c_296,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_295])).

tff(c_253,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_258,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_40,plain,(
    ! [C_43] :
      ( k3_funct_2('#skF_3','#skF_3','#skF_4',C_43) = C_43
      | ~ m1_subset_1(C_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_262,plain,(
    k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_258,c_40])).

tff(c_297,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k3_funct_2(A_112,B_113,C_114,D_115) = k1_funct_1(C_114,D_115)
      | ~ m1_subset_1(D_115,A_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_2(C_114,A_112,B_113)
      | ~ v1_funct_1(C_114)
      | v1_xboole_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_301,plain,(
    ! [B_113,C_114] :
      ( k3_funct_2('#skF_3',B_113,C_114,'#skF_1'('#skF_3','#skF_4')) = k1_funct_1(C_114,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_113)))
      | ~ v1_funct_2(C_114,'#skF_3',B_113)
      | ~ v1_funct_1(C_114)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_258,c_297])).

tff(c_309,plain,(
    ! [B_116,C_117] :
      ( k3_funct_2('#skF_3',B_116,C_117,'#skF_1'('#skF_3','#skF_4')) = k1_funct_1(C_117,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_116)))
      | ~ v1_funct_2(C_117,'#skF_3',B_116)
      | ~ v1_funct_1(C_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_301])).

tff(c_312,plain,
    ( k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_309])).

tff(c_315,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_262,c_312])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_296,c_315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:19:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.29  
% 2.46/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.29  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.46/1.29  
% 2.46/1.29  %Foreground sorts:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Background operators:
% 2.46/1.29  
% 2.46/1.29  
% 2.46/1.29  %Foreground operators:
% 2.46/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.46/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.46/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.46/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.46/1.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.46/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.46/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.29  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.46/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.29  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.46/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.29  
% 2.46/1.30  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.46/1.30  tff(f_132, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 2.46/1.30  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.46/1.30  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.46/1.30  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.46/1.30  tff(f_71, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.46/1.30  tff(f_114, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.46/1.30  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.46/1.30  tff(f_99, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 2.46/1.30  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.46/1.30  tff(f_112, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.46/1.30  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.46/1.30  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.46/1.30  tff(c_64, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.46/1.30  tff(c_67, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_64])).
% 2.46/1.30  tff(c_70, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_67])).
% 2.46/1.30  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.46/1.30  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.46/1.30  tff(c_72, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.30  tff(c_76, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_72])).
% 2.46/1.30  tff(c_84, plain, (![B_60, A_61]: (k1_relat_1(B_60)=A_61 | ~v1_partfun1(B_60, A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.30  tff(c_87, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_partfun1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_84])).
% 2.46/1.30  tff(c_90, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_87])).
% 2.46/1.30  tff(c_91, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_90])).
% 2.46/1.30  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.46/1.30  tff(c_99, plain, (![C_66, A_67, B_68]: (v1_partfun1(C_66, A_67) | ~v1_funct_2(C_66, A_67, B_68) | ~v1_funct_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | v1_xboole_0(B_68))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.46/1.30  tff(c_102, plain, (v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_99])).
% 2.46/1.30  tff(c_105, plain, (v1_partfun1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_102])).
% 2.46/1.30  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_91, c_105])).
% 2.46/1.30  tff(c_108, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_90])).
% 2.46/1.30  tff(c_36, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.46/1.30  tff(c_10, plain, (![B_9]: (r2_hidden('#skF_1'(k1_relat_1(B_9), B_9), k1_relat_1(B_9)) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.30  tff(c_121, plain, (![B_71]: (r2_hidden('#skF_1'(k1_relat_1(B_71), B_71), k1_relat_1(B_71)) | k6_partfun1(k1_relat_1(B_71))=B_71 | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10])).
% 2.46/1.30  tff(c_127, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), k1_relat_1('#skF_4')) | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_108, c_121])).
% 2.46/1.30  tff(c_133, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_46, c_108, c_108, c_127])).
% 2.46/1.30  tff(c_136, plain, (k6_partfun1('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_133])).
% 2.46/1.30  tff(c_38, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.46/1.30  tff(c_137, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_38])).
% 2.46/1.30  tff(c_30, plain, (![D_30, A_22, B_23, C_24]: (k1_funct_1(D_30, '#skF_2'(A_22, B_23, C_24, D_30))!=k1_funct_1(C_24, '#skF_2'(A_22, B_23, C_24, D_30)) | r2_funct_2(A_22, B_23, C_24, D_30) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(D_30, A_22, B_23) | ~v1_funct_1(D_30) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.46/1.30  tff(c_245, plain, (![A_104, B_105, C_106]: (r2_funct_2(A_104, B_105, C_106, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(C_106, A_104, B_105) | ~v1_funct_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(C_106, A_104, B_105) | ~v1_funct_1(C_106))), inference(reflexivity, [status(thm), theory('equality')], [c_30])).
% 2.46/1.30  tff(c_247, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_245])).
% 2.46/1.30  tff(c_250, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_247])).
% 2.46/1.30  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_250])).
% 2.46/1.30  tff(c_254, plain, (k6_partfun1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_133])).
% 2.46/1.30  tff(c_8, plain, (![B_9]: (k1_funct_1(B_9, '#skF_1'(k1_relat_1(B_9), B_9))!='#skF_1'(k1_relat_1(B_9), B_9) | k6_relat_1(k1_relat_1(B_9))=B_9 | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.46/1.30  tff(c_290, plain, (![B_111]: (k1_funct_1(B_111, '#skF_1'(k1_relat_1(B_111), B_111))!='#skF_1'(k1_relat_1(B_111), B_111) | k6_partfun1(k1_relat_1(B_111))=B_111 | ~v1_funct_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 2.46/1.30  tff(c_293, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'(k1_relat_1('#skF_4'), '#skF_4') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_108, c_290])).
% 2.46/1.30  tff(c_295, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'('#skF_3', '#skF_4') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_46, c_108, c_108, c_293])).
% 2.46/1.30  tff(c_296, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_254, c_295])).
% 2.46/1.30  tff(c_253, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_133])).
% 2.46/1.30  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.30  tff(c_258, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_253, c_2])).
% 2.46/1.30  tff(c_40, plain, (![C_43]: (k3_funct_2('#skF_3', '#skF_3', '#skF_4', C_43)=C_43 | ~m1_subset_1(C_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.46/1.30  tff(c_262, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_258, c_40])).
% 2.46/1.30  tff(c_297, plain, (![A_112, B_113, C_114, D_115]: (k3_funct_2(A_112, B_113, C_114, D_115)=k1_funct_1(C_114, D_115) | ~m1_subset_1(D_115, A_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_2(C_114, A_112, B_113) | ~v1_funct_1(C_114) | v1_xboole_0(A_112))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.46/1.30  tff(c_301, plain, (![B_113, C_114]: (k3_funct_2('#skF_3', B_113, C_114, '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1(C_114, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_113))) | ~v1_funct_2(C_114, '#skF_3', B_113) | ~v1_funct_1(C_114) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_258, c_297])).
% 2.46/1.30  tff(c_309, plain, (![B_116, C_117]: (k3_funct_2('#skF_3', B_116, C_117, '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1(C_117, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_116))) | ~v1_funct_2(C_117, '#skF_3', B_116) | ~v1_funct_1(C_117))), inference(negUnitSimplification, [status(thm)], [c_48, c_301])).
% 2.46/1.30  tff(c_312, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_309])).
% 2.46/1.30  tff(c_315, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_262, c_312])).
% 2.46/1.30  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_296, c_315])).
% 2.46/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.30  
% 2.46/1.30  Inference rules
% 2.46/1.30  ----------------------
% 2.46/1.30  #Ref     : 1
% 2.46/1.30  #Sup     : 50
% 2.46/1.30  #Fact    : 0
% 2.46/1.30  #Define  : 0
% 2.46/1.30  #Split   : 3
% 2.46/1.30  #Chain   : 0
% 2.46/1.30  #Close   : 0
% 2.46/1.30  
% 2.46/1.30  Ordering : KBO
% 2.46/1.30  
% 2.46/1.30  Simplification rules
% 2.46/1.30  ----------------------
% 2.46/1.30  #Subsume      : 0
% 2.46/1.30  #Demod        : 93
% 2.46/1.30  #Tautology    : 25
% 2.46/1.30  #SimpNegUnit  : 13
% 2.46/1.31  #BackRed      : 1
% 2.46/1.31  
% 2.46/1.31  #Partial instantiations: 0
% 2.46/1.31  #Strategies tried      : 1
% 2.46/1.31  
% 2.46/1.31  Timing (in seconds)
% 2.46/1.31  ----------------------
% 2.46/1.31  Preprocessing        : 0.32
% 2.46/1.31  Parsing              : 0.17
% 2.46/1.31  CNF conversion       : 0.02
% 2.46/1.31  Main loop            : 0.23
% 2.46/1.31  Inferencing          : 0.09
% 2.46/1.31  Reduction            : 0.07
% 2.46/1.31  Demodulation         : 0.05
% 2.46/1.31  BG Simplification    : 0.02
% 2.46/1.31  Subsumption          : 0.03
% 2.46/1.31  Abstraction          : 0.01
% 2.46/1.31  MUC search           : 0.00
% 2.46/1.31  Cooper               : 0.00
% 2.46/1.31  Total                : 0.59
% 2.46/1.31  Index Insertion      : 0.00
% 2.46/1.31  Index Deletion       : 0.00
% 2.46/1.31  Index Matching       : 0.00
% 2.46/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
