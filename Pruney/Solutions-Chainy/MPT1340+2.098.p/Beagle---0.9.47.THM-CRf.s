%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:44 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  187 (92392 expanded)
%              Number of leaves         :   40 (32480 expanded)
%              Depth                    :   34
%              Number of atoms          :  505 (275703 expanded)
%              Number of equality atoms :  135 (69663 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_198,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_135,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_176,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => v2_funct_1(k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_struct_0(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                  & v2_funct_1(C) )
               => ( k1_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(B)
                  & k2_relset_1(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)) = k2_struct_0(A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_62,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_62])).

tff(c_56,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_69,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_62])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_87,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_50])).

tff(c_88,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_87,c_88])).

tff(c_94,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_91])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_46,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_6,plain,(
    ! [A_6] :
      ( k2_relat_1(k2_funct_1(A_6)) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,(
    ! [A_53,B_54,C_55] :
      ( k2_relset_1(A_53,B_54,C_55) = k2_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_121,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_87,c_117])).

tff(c_48,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_76,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_48])).

tff(c_81,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_76])).

tff(c_123,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_81])).

tff(c_52,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_71,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_52])).

tff(c_86,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_71])).

tff(c_131,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_86])).

tff(c_130,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_87])).

tff(c_128,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_121])).

tff(c_265,plain,(
    ! [A_84,B_85,C_86] :
      ( k2_tops_2(A_84,B_85,C_86) = k2_funct_1(C_86)
      | ~ v2_funct_1(C_86)
      | k2_relset_1(A_84,B_85,C_86) != B_85
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85)))
      | ~ v1_funct_2(C_86,A_84,B_85)
      | ~ v1_funct_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_271,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_265])).

tff(c_275,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_128,c_46,c_271])).

tff(c_32,plain,(
    ! [A_25,B_26,C_27] :
      ( m1_subset_1(k2_tops_2(A_25,B_26,C_27),k1_zfmisc_1(k2_zfmisc_1(B_26,A_25)))
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_2(C_27,A_25,B_26)
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_285,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_32])).

tff(c_289,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_130,c_285])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k2_relset_1(A_11,B_12,C_13) = k2_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_342,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_289,c_16])).

tff(c_225,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_funct_1(k2_funct_1(C_73))
      | k2_relset_1(A_74,B_75,C_73) != B_75
      | ~ v2_funct_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75)))
      | ~ v1_funct_2(C_73,A_74,B_75)
      | ~ v1_funct_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_231,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_225])).

tff(c_235,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_46,c_128,c_231])).

tff(c_245,plain,(
    ! [C_78,B_79,A_80] :
      ( v1_funct_2(k2_funct_1(C_78),B_79,A_80)
      | k2_relset_1(A_80,B_79,C_78) != B_79
      | ~ v2_funct_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_2(C_78,A_80,B_79)
      | ~ v1_funct_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_251,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_245])).

tff(c_255,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_46,c_128,c_251])).

tff(c_26,plain,(
    ! [C_20,A_18,B_19] :
      ( v1_funct_1(k2_funct_1(C_20))
      | k2_relset_1(A_18,B_19,C_20) != B_19
      | ~ v2_funct_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_301,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_289,c_26])).

tff(c_329,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_255,c_301])).

tff(c_390,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_329])).

tff(c_391,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_132,plain,(
    u1_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_69])).

tff(c_454,plain,(
    ! [A_100,B_101,C_102] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_100),u1_struct_0(B_101),C_102))
      | ~ v2_funct_1(C_102)
      | k2_relset_1(u1_struct_0(A_100),u1_struct_0(B_101),C_102) != k2_struct_0(B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_100),u1_struct_0(B_101))))
      | ~ v1_funct_2(C_102,u1_struct_0(A_100),u1_struct_0(B_101))
      | ~ v1_funct_1(C_102)
      | ~ l1_struct_0(B_101)
      | ~ l1_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_471,plain,(
    ! [B_101,C_102] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0(B_101),C_102))
      | ~ v2_funct_1(C_102)
      | k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0(B_101),C_102) != k2_struct_0(B_101)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_101))))
      | ~ v1_funct_2(C_102,u1_struct_0('#skF_1'),u1_struct_0(B_101))
      | ~ v1_funct_1(C_102)
      | ~ l1_struct_0(B_101)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_454])).

tff(c_519,plain,(
    ! [B_109,C_110] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0(B_109),C_110))
      | ~ v2_funct_1(C_110)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0(B_109),C_110) != k2_struct_0(B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_110,k2_struct_0('#skF_1'),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ l1_struct_0(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_70,c_70,c_70,c_471])).

tff(c_530,plain,(
    ! [C_110] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_110))
      | ~ v2_funct_1(C_110)
      | k2_relset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'),C_110) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_110,k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_110)
      | ~ l1_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_519])).

tff(c_582,plain,(
    ! [C_117] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_117))
      | ~ v2_funct_1(C_117)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_117) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_117,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_132,c_132,c_123,c_132,c_530])).

tff(c_593,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_582])).

tff(c_598,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_128,c_46,c_275,c_593])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_598])).

tff(c_601,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_616,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_601])).

tff(c_619,plain,
    ( k2_struct_0('#skF_1') != k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_616])).

tff(c_621,plain,(
    k2_struct_0('#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_619])).

tff(c_193,plain,(
    ! [A_67,B_68,C_69] :
      ( m1_subset_1(k2_tops_2(A_67,B_68,C_69),k1_zfmisc_1(k2_zfmisc_1(B_68,A_67)))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(C_69,A_67,B_68)
      | ~ v1_funct_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,(
    ! [A_67,B_68,C_69] :
      ( v1_relat_1(k2_tops_2(A_67,B_68,C_69))
      | ~ v1_relat_1(k2_zfmisc_1(B_68,A_67))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ v1_funct_2(C_69,A_67,B_68)
      | ~ v1_funct_1(C_69) ) ),
    inference(resolution,[status(thm)],[c_193,c_2])).

tff(c_214,plain,(
    ! [A_70,B_71,C_72] :
      ( v1_relat_1(k2_tops_2(A_70,B_71,C_72))
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ v1_funct_2(C_72,A_70,B_71)
      | ~ v1_funct_1(C_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_206])).

tff(c_220,plain,
    ( v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_214])).

tff(c_224,plain,(
    v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_220])).

tff(c_276,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_224])).

tff(c_602,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_relat_1(k2_funct_1(A_6)) = k2_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k2_funct_1(A_7)) = k6_relat_1(k1_relat_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_236,plain,(
    ! [A_76,B_77] :
      ( k2_funct_1(A_76) = B_77
      | k6_relat_1(k2_relat_1(A_76)) != k5_relat_1(B_77,A_76)
      | k2_relat_1(B_77) != k1_relat_1(A_76)
      | ~ v2_funct_1(A_76)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_935,plain,(
    ! [A_161] :
      ( k2_funct_1(k2_funct_1(A_161)) = A_161
      | k6_relat_1(k2_relat_1(k2_funct_1(A_161))) != k6_relat_1(k1_relat_1(A_161))
      | k1_relat_1(k2_funct_1(A_161)) != k2_relat_1(A_161)
      | ~ v2_funct_1(k2_funct_1(A_161))
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161)
      | ~ v1_funct_1(k2_funct_1(A_161))
      | ~ v1_relat_1(k2_funct_1(A_161))
      | ~ v2_funct_1(A_161)
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_236])).

tff(c_940,plain,(
    ! [A_162] :
      ( k2_funct_1(k2_funct_1(A_162)) = A_162
      | k1_relat_1(k2_funct_1(A_162)) != k2_relat_1(A_162)
      | ~ v2_funct_1(k2_funct_1(A_162))
      | ~ v1_funct_1(k2_funct_1(A_162))
      | ~ v1_relat_1(k2_funct_1(A_162))
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_935])).

tff(c_943,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_602,c_940])).

tff(c_946,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_276,c_235,c_943])).

tff(c_947,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_946])).

tff(c_950,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_947])).

tff(c_954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_950])).

tff(c_955,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_946])).

tff(c_978,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_8])).

tff(c_997,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_235,c_602,c_978])).

tff(c_1070,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_342])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_829,plain,(
    ! [B_147,A_148,C_149] :
      ( k2_relset_1(u1_struct_0(B_147),u1_struct_0(A_148),k2_tops_2(u1_struct_0(A_148),u1_struct_0(B_147),C_149)) = k2_struct_0(A_148)
      | ~ v2_funct_1(C_149)
      | k2_relset_1(u1_struct_0(A_148),u1_struct_0(B_147),C_149) != k2_struct_0(B_147)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148),u1_struct_0(B_147))))
      | ~ v1_funct_2(C_149,u1_struct_0(A_148),u1_struct_0(B_147))
      | ~ v1_funct_1(C_149)
      | ~ l1_struct_0(B_147)
      | v2_struct_0(B_147)
      | ~ l1_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_838,plain,(
    ! [A_148,C_149] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_148),k2_tops_2(u1_struct_0(A_148),u1_struct_0('#skF_2'),C_149)) = k2_struct_0(A_148)
      | ~ v2_funct_1(C_149)
      | k2_relset_1(u1_struct_0(A_148),u1_struct_0('#skF_2'),C_149) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_149,u1_struct_0(A_148),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_149)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_829])).

tff(c_863,plain,(
    ! [A_148,C_149] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_148),k2_tops_2(u1_struct_0(A_148),k2_relat_1('#skF_3'),C_149)) = k2_struct_0(A_148)
      | ~ v2_funct_1(C_149)
      | k2_relset_1(u1_struct_0(A_148),k2_relat_1('#skF_3'),C_149) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_149,u1_struct_0(A_148),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_149)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_132,c_132,c_123,c_132,c_132,c_838])).

tff(c_906,plain,(
    ! [A_159,C_160] :
      ( k2_relset_1(k2_relat_1('#skF_3'),u1_struct_0(A_159),k2_tops_2(u1_struct_0(A_159),k2_relat_1('#skF_3'),C_160)) = k2_struct_0(A_159)
      | ~ v2_funct_1(C_160)
      | k2_relset_1(u1_struct_0(A_159),k2_relat_1('#skF_3'),C_160) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_160,u1_struct_0(A_159),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_160)
      | ~ l1_struct_0(A_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_863])).

tff(c_921,plain,(
    ! [C_160] :
      ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_160)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_160)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_160) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_160,u1_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_160)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_906])).

tff(c_1415,plain,(
    ! [C_198] :
      ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_198)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_198)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),C_198) != k2_relat_1('#skF_3')
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_198,k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_70,c_70,c_70,c_70,c_921])).

tff(c_1424,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_1415])).

tff(c_1428,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_130,c_128,c_46,c_1070,c_1424])).

tff(c_1430,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_621,c_1428])).

tff(c_1432,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_1470,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_6])).

tff(c_1479,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_1470])).

tff(c_181,plain,(
    ! [A_61,B_62,D_63] :
      ( r2_funct_2(A_61,B_62,D_63,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(D_63,A_61,B_62)
      | ~ v1_funct_1(D_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_183,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_181])).

tff(c_186,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_131,c_183])).

tff(c_1492,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_186])).

tff(c_14,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1467,plain,(
    ! [B_10] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_10
      | k5_relat_1(B_10,k2_funct_1('#skF_3')) != k6_relat_1(k2_struct_0('#skF_1'))
      | k2_relat_1(B_10) != k1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_14])).

tff(c_1477,plain,(
    ! [B_10] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_10
      | k5_relat_1(B_10,k2_funct_1('#skF_3')) != k6_relat_1(k2_struct_0('#skF_1'))
      | k2_relat_1(B_10) != k1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_235,c_602,c_1467])).

tff(c_2010,plain,(
    ! [B_221] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_221
      | k5_relat_1(B_221,k2_funct_1('#skF_3')) != k6_relat_1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_221) != k1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1477])).

tff(c_2018,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2010])).

tff(c_2024,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_2018])).

tff(c_2025,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2024])).

tff(c_2050,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2025])).

tff(c_2054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_2050])).

tff(c_2055,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2024])).

tff(c_1491,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_255])).

tff(c_1489,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_289])).

tff(c_1464,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_342])).

tff(c_1747,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1479,c_1464])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] :
      ( k2_tops_2(A_22,B_23,C_24) = k2_funct_1(C_24)
      | ~ v2_funct_1(C_24)
      | k2_relset_1(A_22,B_23,C_24) != B_23
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1760,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1489,c_30])).

tff(c_1787,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_1491,c_1747,c_602,c_1760])).

tff(c_1821,plain,
    ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_32])).

tff(c_1825,plain,(
    m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_1491,c_1489,c_1821])).

tff(c_1878,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1825,c_16])).

tff(c_1431,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_601])).

tff(c_24,plain,(
    ! [C_20,B_19,A_18] :
      ( v1_funct_2(k2_funct_1(C_20),B_19,A_18)
      | k2_relset_1(A_18,B_19,C_20) != B_19
      | ~ v2_funct_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1765,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1489,c_24])).

tff(c_1793,plain,(
    v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_1491,c_602,c_1747,c_1765])).

tff(c_1837,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1825,c_26])).

tff(c_1865,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3'))) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1793,c_1837])).

tff(c_1981,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_1865])).

tff(c_1982,plain,(
    ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1981])).

tff(c_2059,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2055,c_1982])).

tff(c_2074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2059])).

tff(c_2075,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) != k2_relat_1('#skF_3')
    | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_1981])).

tff(c_2077,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2075])).

tff(c_2080,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2077])).

tff(c_2082,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_235,c_602,c_2080])).

tff(c_2107,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2082])).

tff(c_2111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_2107])).

tff(c_2113,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2075])).

tff(c_2120,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2113,c_6])).

tff(c_2129,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_235,c_602,c_2120])).

tff(c_2204,plain,(
    ! [B_232] :
      ( k2_funct_1(k2_funct_1('#skF_3')) = B_232
      | k5_relat_1(B_232,k2_funct_1('#skF_3')) != k6_relat_1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_232) != k2_relat_1('#skF_3')
      | ~ v1_funct_1(B_232)
      | ~ v1_relat_1(B_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_1479,c_1477])).

tff(c_2212,plain,
    ( k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2204])).

tff(c_2218,plain,(
    k2_funct_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_54,c_46,c_2212])).

tff(c_44,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_122,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_70,c_70,c_69,c_69,c_69,c_44])).

tff(c_129,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_123,c_123,c_122])).

tff(c_279,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_129])).

tff(c_1488,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1479,c_279])).

tff(c_1951,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_1488])).

tff(c_2249,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2218,c_1951])).

tff(c_2266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_2249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.90  
% 4.71/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.90  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k6_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.09/1.90  
% 5.09/1.90  %Foreground sorts:
% 5.09/1.90  
% 5.09/1.90  
% 5.09/1.90  %Background operators:
% 5.09/1.90  
% 5.09/1.90  
% 5.09/1.90  %Foreground operators:
% 5.09/1.90  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.09/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.09/1.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.09/1.90  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.09/1.90  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.09/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/1.90  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.09/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.09/1.90  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 5.09/1.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.09/1.90  tff('#skF_2', type, '#skF_2': $i).
% 5.09/1.90  tff('#skF_3', type, '#skF_3': $i).
% 5.09/1.90  tff('#skF_1', type, '#skF_1': $i).
% 5.09/1.90  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.09/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.09/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.09/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.09/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.09/1.90  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.09/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.09/1.90  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.09/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.09/1.90  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.09/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.09/1.90  
% 5.09/1.93  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.09/1.93  tff(f_198, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 5.09/1.93  tff(f_111, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 5.09/1.93  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.09/1.93  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 5.09/1.93  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.09/1.93  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 5.09/1.93  tff(f_135, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v1_funct_1(k2_tops_2(A, B, C)) & v1_funct_2(k2_tops_2(A, B, C), B, A)) & m1_subset_1(k2_tops_2(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 5.09/1.93  tff(f_107, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 5.09/1.93  tff(f_176, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => v2_funct_1(k2_tops_2(u1_struct_0(A), u1_struct_0(B), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_tops_2)).
% 5.09/1.93  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 5.09/1.93  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 5.09/1.93  tff(f_158, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 5.09/1.93  tff(f_91, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 5.09/1.93  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.09/1.93  tff(c_60, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_62, plain, (![A_48]: (u1_struct_0(A_48)=k2_struct_0(A_48) | ~l1_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.09/1.93  tff(c_70, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_60, c_62])).
% 5.09/1.93  tff(c_56, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_69, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_62])).
% 5.09/1.93  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_87, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_50])).
% 5.09/1.93  tff(c_88, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.93  tff(c_91, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_87, c_88])).
% 5.09/1.93  tff(c_94, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_91])).
% 5.09/1.93  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_46, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_6, plain, (![A_6]: (k2_relat_1(k2_funct_1(A_6))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.09/1.93  tff(c_117, plain, (![A_53, B_54, C_55]: (k2_relset_1(A_53, B_54, C_55)=k2_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.09/1.93  tff(c_121, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_87, c_117])).
% 5.09/1.93  tff(c_48, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_76, plain, (k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_48])).
% 5.09/1.93  tff(c_81, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_76])).
% 5.09/1.93  tff(c_123, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_81])).
% 5.09/1.93  tff(c_52, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_71, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_52])).
% 5.09/1.93  tff(c_86, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_71])).
% 5.09/1.93  tff(c_131, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_86])).
% 5.09/1.93  tff(c_130, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_87])).
% 5.09/1.93  tff(c_128, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_121])).
% 5.09/1.93  tff(c_265, plain, (![A_84, B_85, C_86]: (k2_tops_2(A_84, B_85, C_86)=k2_funct_1(C_86) | ~v2_funct_1(C_86) | k2_relset_1(A_84, B_85, C_86)!=B_85 | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))) | ~v1_funct_2(C_86, A_84, B_85) | ~v1_funct_1(C_86))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.09/1.93  tff(c_271, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_265])).
% 5.09/1.93  tff(c_275, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_128, c_46, c_271])).
% 5.09/1.93  tff(c_32, plain, (![A_25, B_26, C_27]: (m1_subset_1(k2_tops_2(A_25, B_26, C_27), k1_zfmisc_1(k2_zfmisc_1(B_26, A_25))) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_2(C_27, A_25, B_26) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.09/1.93  tff(c_285, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_275, c_32])).
% 5.09/1.93  tff(c_289, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_130, c_285])).
% 5.09/1.93  tff(c_16, plain, (![A_11, B_12, C_13]: (k2_relset_1(A_11, B_12, C_13)=k2_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.09/1.93  tff(c_342, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_289, c_16])).
% 5.09/1.93  tff(c_225, plain, (![C_73, A_74, B_75]: (v1_funct_1(k2_funct_1(C_73)) | k2_relset_1(A_74, B_75, C_73)!=B_75 | ~v2_funct_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))) | ~v1_funct_2(C_73, A_74, B_75) | ~v1_funct_1(C_73))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.09/1.93  tff(c_231, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_225])).
% 5.09/1.93  tff(c_235, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_46, c_128, c_231])).
% 5.09/1.93  tff(c_245, plain, (![C_78, B_79, A_80]: (v1_funct_2(k2_funct_1(C_78), B_79, A_80) | k2_relset_1(A_80, B_79, C_78)!=B_79 | ~v2_funct_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_2(C_78, A_80, B_79) | ~v1_funct_1(C_78))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.09/1.93  tff(c_251, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_245])).
% 5.09/1.93  tff(c_255, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_46, c_128, c_251])).
% 5.09/1.93  tff(c_26, plain, (![C_20, A_18, B_19]: (v1_funct_1(k2_funct_1(C_20)) | k2_relset_1(A_18, B_19, C_20)!=B_19 | ~v2_funct_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.09/1.93  tff(c_301, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_289, c_26])).
% 5.09/1.93  tff(c_329, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_255, c_301])).
% 5.09/1.93  tff(c_390, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relat_1(k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_329])).
% 5.09/1.93  tff(c_391, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_390])).
% 5.09/1.93  tff(c_132, plain, (u1_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_69])).
% 5.09/1.93  tff(c_454, plain, (![A_100, B_101, C_102]: (v2_funct_1(k2_tops_2(u1_struct_0(A_100), u1_struct_0(B_101), C_102)) | ~v2_funct_1(C_102) | k2_relset_1(u1_struct_0(A_100), u1_struct_0(B_101), C_102)!=k2_struct_0(B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_100), u1_struct_0(B_101)))) | ~v1_funct_2(C_102, u1_struct_0(A_100), u1_struct_0(B_101)) | ~v1_funct_1(C_102) | ~l1_struct_0(B_101) | ~l1_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_176])).
% 5.09/1.93  tff(c_471, plain, (![B_101, C_102]: (v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0(B_101), C_102)) | ~v2_funct_1(C_102) | k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0(B_101), C_102)!=k2_struct_0(B_101) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_101)))) | ~v1_funct_2(C_102, u1_struct_0('#skF_1'), u1_struct_0(B_101)) | ~v1_funct_1(C_102) | ~l1_struct_0(B_101) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_454])).
% 5.09/1.93  tff(c_519, plain, (![B_109, C_110]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0(B_109), C_110)) | ~v2_funct_1(C_110) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0(B_109), C_110)!=k2_struct_0(B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), u1_struct_0(B_109)))) | ~v1_funct_2(C_110, k2_struct_0('#skF_1'), u1_struct_0(B_109)) | ~v1_funct_1(C_110) | ~l1_struct_0(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_70, c_70, c_70, c_471])).
% 5.09/1.93  tff(c_530, plain, (![C_110]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_110)) | ~v2_funct_1(C_110) | k2_relset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2'), C_110)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_110, k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_110) | ~l1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_519])).
% 5.09/1.93  tff(c_582, plain, (![C_117]: (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_117)) | ~v2_funct_1(C_117) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_117)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_117, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_117))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_132, c_132, c_123, c_132, c_530])).
% 5.09/1.93  tff(c_593, plain, (v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')) | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_582])).
% 5.09/1.93  tff(c_598, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_128, c_46, c_275, c_593])).
% 5.09/1.93  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_598])).
% 5.09/1.93  tff(c_601, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_390])).
% 5.09/1.93  tff(c_616, plain, (k2_relat_1(k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_601])).
% 5.09/1.93  tff(c_619, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6, c_616])).
% 5.09/1.93  tff(c_621, plain, (k2_struct_0('#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_619])).
% 5.09/1.93  tff(c_193, plain, (![A_67, B_68, C_69]: (m1_subset_1(k2_tops_2(A_67, B_68, C_69), k1_zfmisc_1(k2_zfmisc_1(B_68, A_67))) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(C_69, A_67, B_68) | ~v1_funct_1(C_69))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.09/1.93  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.93  tff(c_206, plain, (![A_67, B_68, C_69]: (v1_relat_1(k2_tops_2(A_67, B_68, C_69)) | ~v1_relat_1(k2_zfmisc_1(B_68, A_67)) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~v1_funct_2(C_69, A_67, B_68) | ~v1_funct_1(C_69))), inference(resolution, [status(thm)], [c_193, c_2])).
% 5.09/1.93  tff(c_214, plain, (![A_70, B_71, C_72]: (v1_relat_1(k2_tops_2(A_70, B_71, C_72)) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~v1_funct_2(C_72, A_70, B_71) | ~v1_funct_1(C_72))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_206])).
% 5.09/1.93  tff(c_220, plain, (v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_214])).
% 5.09/1.93  tff(c_224, plain, (v1_relat_1(k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_220])).
% 5.09/1.93  tff(c_276, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_224])).
% 5.09/1.93  tff(c_602, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_390])).
% 5.09/1.93  tff(c_8, plain, (![A_6]: (k1_relat_1(k2_funct_1(A_6))=k2_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.09/1.93  tff(c_12, plain, (![A_7]: (k5_relat_1(A_7, k2_funct_1(A_7))=k6_relat_1(k1_relat_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.09/1.93  tff(c_236, plain, (![A_76, B_77]: (k2_funct_1(A_76)=B_77 | k6_relat_1(k2_relat_1(A_76))!=k5_relat_1(B_77, A_76) | k2_relat_1(B_77)!=k1_relat_1(A_76) | ~v2_funct_1(A_76) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.09/1.93  tff(c_935, plain, (![A_161]: (k2_funct_1(k2_funct_1(A_161))=A_161 | k6_relat_1(k2_relat_1(k2_funct_1(A_161)))!=k6_relat_1(k1_relat_1(A_161)) | k1_relat_1(k2_funct_1(A_161))!=k2_relat_1(A_161) | ~v2_funct_1(k2_funct_1(A_161)) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161) | ~v1_funct_1(k2_funct_1(A_161)) | ~v1_relat_1(k2_funct_1(A_161)) | ~v2_funct_1(A_161) | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(superposition, [status(thm), theory('equality')], [c_12, c_236])).
% 5.09/1.93  tff(c_940, plain, (![A_162]: (k2_funct_1(k2_funct_1(A_162))=A_162 | k1_relat_1(k2_funct_1(A_162))!=k2_relat_1(A_162) | ~v2_funct_1(k2_funct_1(A_162)) | ~v1_funct_1(k2_funct_1(A_162)) | ~v1_relat_1(k2_funct_1(A_162)) | ~v2_funct_1(A_162) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(superposition, [status(thm), theory('equality')], [c_6, c_935])).
% 5.09/1.93  tff(c_943, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_602, c_940])).
% 5.09/1.93  tff(c_946, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_276, c_235, c_943])).
% 5.09/1.93  tff(c_947, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_946])).
% 5.09/1.93  tff(c_950, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_947])).
% 5.09/1.93  tff(c_954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_950])).
% 5.09/1.93  tff(c_955, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_946])).
% 5.09/1.93  tff(c_978, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_955, c_8])).
% 5.09/1.93  tff(c_997, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_235, c_602, c_978])).
% 5.09/1.93  tff(c_1070, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_997, c_342])).
% 5.09/1.93  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_829, plain, (![B_147, A_148, C_149]: (k2_relset_1(u1_struct_0(B_147), u1_struct_0(A_148), k2_tops_2(u1_struct_0(A_148), u1_struct_0(B_147), C_149))=k2_struct_0(A_148) | ~v2_funct_1(C_149) | k2_relset_1(u1_struct_0(A_148), u1_struct_0(B_147), C_149)!=k2_struct_0(B_147) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148), u1_struct_0(B_147)))) | ~v1_funct_2(C_149, u1_struct_0(A_148), u1_struct_0(B_147)) | ~v1_funct_1(C_149) | ~l1_struct_0(B_147) | v2_struct_0(B_147) | ~l1_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.09/1.93  tff(c_838, plain, (![A_148, C_149]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_148), k2_tops_2(u1_struct_0(A_148), u1_struct_0('#skF_2'), C_149))=k2_struct_0(A_148) | ~v2_funct_1(C_149) | k2_relset_1(u1_struct_0(A_148), u1_struct_0('#skF_2'), C_149)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_149, u1_struct_0(A_148), u1_struct_0('#skF_2')) | ~v1_funct_1(C_149) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_148))), inference(superposition, [status(thm), theory('equality')], [c_132, c_829])).
% 5.09/1.93  tff(c_863, plain, (![A_148, C_149]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_148), k2_tops_2(u1_struct_0(A_148), k2_relat_1('#skF_3'), C_149))=k2_struct_0(A_148) | ~v2_funct_1(C_149) | k2_relset_1(u1_struct_0(A_148), k2_relat_1('#skF_3'), C_149)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_148), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_149, u1_struct_0(A_148), k2_relat_1('#skF_3')) | ~v1_funct_1(C_149) | v2_struct_0('#skF_2') | ~l1_struct_0(A_148))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_132, c_132, c_123, c_132, c_132, c_838])).
% 5.09/1.93  tff(c_906, plain, (![A_159, C_160]: (k2_relset_1(k2_relat_1('#skF_3'), u1_struct_0(A_159), k2_tops_2(u1_struct_0(A_159), k2_relat_1('#skF_3'), C_160))=k2_struct_0(A_159) | ~v2_funct_1(C_160) | k2_relset_1(u1_struct_0(A_159), k2_relat_1('#skF_3'), C_160)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_159), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_160, u1_struct_0(A_159), k2_relat_1('#skF_3')) | ~v1_funct_1(C_160) | ~l1_struct_0(A_159))), inference(negUnitSimplification, [status(thm)], [c_58, c_863])).
% 5.09/1.93  tff(c_921, plain, (![C_160]: (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_160))=k2_struct_0('#skF_1') | ~v2_funct_1(C_160) | k2_relset_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_160)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_160, u1_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_160) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_906])).
% 5.09/1.93  tff(c_1415, plain, (![C_198]: (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_198))=k2_struct_0('#skF_1') | ~v2_funct_1(C_198) | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), C_198)!=k2_relat_1('#skF_3') | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_198, k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_198))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_70, c_70, c_70, c_70, c_921])).
% 5.09/1.93  tff(c_1424, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_275, c_1415])).
% 5.09/1.93  tff(c_1428, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_130, c_128, c_46, c_1070, c_1424])).
% 5.09/1.93  tff(c_1430, plain, $false, inference(negUnitSimplification, [status(thm)], [c_621, c_1428])).
% 5.09/1.93  tff(c_1432, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_601])).
% 5.09/1.93  tff(c_1470, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1432, c_6])).
% 5.09/1.93  tff(c_1479, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_1470])).
% 5.09/1.93  tff(c_181, plain, (![A_61, B_62, D_63]: (r2_funct_2(A_61, B_62, D_63, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(D_63, A_61, B_62) | ~v1_funct_1(D_63))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.09/1.93  tff(c_183, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_181])).
% 5.09/1.93  tff(c_186, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_131, c_183])).
% 5.09/1.93  tff(c_1492, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_186])).
% 5.09/1.93  tff(c_14, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.09/1.93  tff(c_1467, plain, (![B_10]: (k2_funct_1(k2_funct_1('#skF_3'))=B_10 | k5_relat_1(B_10, k2_funct_1('#skF_3'))!=k6_relat_1(k2_struct_0('#skF_1')) | k2_relat_1(B_10)!=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1432, c_14])).
% 5.09/1.93  tff(c_1477, plain, (![B_10]: (k2_funct_1(k2_funct_1('#skF_3'))=B_10 | k5_relat_1(B_10, k2_funct_1('#skF_3'))!=k6_relat_1(k2_struct_0('#skF_1')) | k2_relat_1(B_10)!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_235, c_602, c_1467])).
% 5.09/1.93  tff(c_2010, plain, (![B_221]: (k2_funct_1(k2_funct_1('#skF_3'))=B_221 | k5_relat_1(B_221, k2_funct_1('#skF_3'))!=k6_relat_1(k1_relat_1('#skF_3')) | k2_relat_1(B_221)!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(B_221) | ~v1_relat_1(B_221))), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1477])).
% 5.09/1.93  tff(c_2018, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2010])).
% 5.09/1.93  tff(c_2024, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_2018])).
% 5.09/1.93  tff(c_2025, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2024])).
% 5.09/1.93  tff(c_2050, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_2025])).
% 5.09/1.93  tff(c_2054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_2050])).
% 5.09/1.93  tff(c_2055, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_2024])).
% 5.09/1.93  tff(c_1491, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_255])).
% 5.09/1.93  tff(c_1489, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_289])).
% 5.09/1.93  tff(c_1464, plain, (k2_relset_1(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_342])).
% 5.09/1.93  tff(c_1747, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1479, c_1464])).
% 5.09/1.93  tff(c_30, plain, (![A_22, B_23, C_24]: (k2_tops_2(A_22, B_23, C_24)=k2_funct_1(C_24) | ~v2_funct_1(C_24) | k2_relset_1(A_22, B_23, C_24)!=B_23 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_2(C_24, A_22, B_23) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.09/1.93  tff(c_1760, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1489, c_30])).
% 5.09/1.93  tff(c_1787, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_1491, c_1747, c_602, c_1760])).
% 5.09/1.93  tff(c_1821, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1787, c_32])).
% 5.09/1.93  tff(c_1825, plain, (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_1491, c_1489, c_1821])).
% 5.09/1.93  tff(c_1878, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1825, c_16])).
% 5.09/1.93  tff(c_1431, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_601])).
% 5.09/1.93  tff(c_24, plain, (![C_20, B_19, A_18]: (v1_funct_2(k2_funct_1(C_20), B_19, A_18) | k2_relset_1(A_18, B_19, C_20)!=B_19 | ~v2_funct_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(C_20, A_18, B_19) | ~v1_funct_1(C_20))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.09/1.93  tff(c_1765, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1489, c_24])).
% 5.09/1.93  tff(c_1793, plain, (v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_1491, c_602, c_1747, c_1765])).
% 5.09/1.93  tff(c_1837, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_1825, c_26])).
% 5.09/1.93  tff(c_1865, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1431, c_1793, c_1837])).
% 5.09/1.93  tff(c_1981, plain, (v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1878, c_1865])).
% 5.09/1.93  tff(c_1982, plain, (~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1981])).
% 5.09/1.93  tff(c_2059, plain, (~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2055, c_1982])).
% 5.09/1.93  tff(c_2074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2059])).
% 5.09/1.93  tff(c_2075, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))!=k2_relat_1('#skF_3') | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_1981])).
% 5.09/1.93  tff(c_2077, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_2075])).
% 5.09/1.93  tff(c_2080, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2077])).
% 5.09/1.93  tff(c_2082, plain, (k1_relat_1(k2_funct_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_235, c_602, c_2080])).
% 5.09/1.93  tff(c_2107, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_2082])).
% 5.09/1.93  tff(c_2111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_2107])).
% 5.09/1.93  tff(c_2113, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2075])).
% 5.09/1.93  tff(c_2120, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2113, c_6])).
% 5.09/1.93  tff(c_2129, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_276, c_235, c_602, c_2120])).
% 5.09/1.93  tff(c_2204, plain, (![B_232]: (k2_funct_1(k2_funct_1('#skF_3'))=B_232 | k5_relat_1(B_232, k2_funct_1('#skF_3'))!=k6_relat_1(k1_relat_1('#skF_3')) | k2_relat_1(B_232)!=k2_relat_1('#skF_3') | ~v1_funct_1(B_232) | ~v1_relat_1(B_232))), inference(demodulation, [status(thm), theory('equality')], [c_2129, c_1479, c_1477])).
% 5.09/1.93  tff(c_2212, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2204])).
% 5.09/1.93  tff(c_2218, plain, (k2_funct_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_54, c_46, c_2212])).
% 5.09/1.93  tff(c_44, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 5.09/1.93  tff(c_122, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_70, c_70, c_69, c_69, c_69, c_44])).
% 5.09/1.93  tff(c_129, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_123, c_123, c_122])).
% 5.09/1.93  tff(c_279, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_129])).
% 5.09/1.93  tff(c_1488, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1479, c_279])).
% 5.09/1.93  tff(c_1951, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_1488])).
% 5.09/1.93  tff(c_2249, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2218, c_1951])).
% 5.09/1.93  tff(c_2266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1492, c_2249])).
% 5.09/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.09/1.93  
% 5.09/1.93  Inference rules
% 5.09/1.93  ----------------------
% 5.09/1.93  #Ref     : 0
% 5.09/1.93  #Sup     : 434
% 5.09/1.93  #Fact    : 0
% 5.09/1.93  #Define  : 0
% 5.09/1.93  #Split   : 6
% 5.09/1.93  #Chain   : 0
% 5.09/1.93  #Close   : 0
% 5.09/1.93  
% 5.09/1.93  Ordering : KBO
% 5.09/1.93  
% 5.09/1.93  Simplification rules
% 5.09/1.93  ----------------------
% 5.09/1.93  #Subsume      : 33
% 5.09/1.93  #Demod        : 1242
% 5.09/1.93  #Tautology    : 194
% 5.09/1.93  #SimpNegUnit  : 10
% 5.09/1.93  #BackRed      : 64
% 5.09/1.93  
% 5.09/1.93  #Partial instantiations: 0
% 5.09/1.93  #Strategies tried      : 1
% 5.09/1.93  
% 5.09/1.93  Timing (in seconds)
% 5.09/1.93  ----------------------
% 5.09/1.93  Preprocessing        : 0.36
% 5.09/1.93  Parsing              : 0.19
% 5.09/1.93  CNF conversion       : 0.02
% 5.09/1.93  Main loop            : 0.76
% 5.09/1.93  Inferencing          : 0.25
% 5.09/1.93  Reduction            : 0.28
% 5.09/1.93  Demodulation         : 0.21
% 5.09/1.93  BG Simplification    : 0.04
% 5.09/1.93  Subsumption          : 0.13
% 5.09/1.93  Abstraction          : 0.04
% 5.09/1.93  MUC search           : 0.00
% 5.09/1.93  Cooper               : 0.00
% 5.09/1.93  Total                : 1.18
% 5.09/1.93  Index Insertion      : 0.00
% 5.09/1.93  Index Deletion       : 0.00
% 5.09/1.93  Index Matching       : 0.00
% 5.09/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
