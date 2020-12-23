%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1340+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:49 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   99 (1249 expanded)
%              Number of leaves         :   31 ( 471 expanded)
%              Depth                    :   15
%              Number of atoms          :  263 (4103 expanded)
%              Number of equality atoms :   50 ( 895 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_127,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_tops_2(A,B,C))
        & v1_funct_2(k2_tops_2(A,B,C),B,A)
        & m1_subset_1(k2_tops_2(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

tff(f_119,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(c_44,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_45,plain,(
    ! [A_35] :
      ( u1_struct_0(A_35) = k2_struct_0(A_35)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_45])).

tff(c_40,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_45])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_63,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_52,c_34])).

tff(c_67,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_71,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_67])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_26,plain,(
    ! [A_30] :
      ( k2_funct_1(k2_funct_1(A_30)) = A_30
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_36])).

tff(c_64,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_54])).

tff(c_32,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_72,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_52,c_32])).

tff(c_137,plain,(
    ! [A_54,B_55,C_56] :
      ( k2_tops_2(A_54,B_55,C_56) = k2_funct_1(C_56)
      | ~ v2_funct_1(C_56)
      | k2_relset_1(A_54,B_55,C_56) != B_55
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55)))
      | ~ v1_funct_2(C_56,A_54,B_55)
      | ~ v1_funct_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_143,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_137])).

tff(c_147,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_72,c_30,c_143])).

tff(c_101,plain,(
    ! [A_42,B_43,C_44] :
      ( v1_funct_1(k2_tops_2(A_42,B_43,C_44))
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(C_44,A_42,B_43)
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_104,plain,
    ( v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_101])).

tff(c_107,plain,(
    v1_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_104])).

tff(c_150,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_107])).

tff(c_108,plain,(
    ! [A_45,B_46,C_47] :
      ( v1_funct_2(k2_tops_2(A_45,B_46,C_47),B_46,A_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_108])).

tff(c_113,plain,(
    v1_funct_2(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_110])).

tff(c_149,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_113])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k2_tops_2(A_9,B_10,C_11),k1_zfmisc_1(k2_zfmisc_1(B_10,A_9)))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(C_11,A_9,B_10)
      | ~ v1_funct_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_155,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_12])).

tff(c_159,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_63,c_155])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( k2_tops_2(A_5,B_6,C_7) = k2_funct_1(C_7)
      | ~ v2_funct_1(C_7)
      | k2_relset_1(A_5,B_6,C_7) != B_6
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_5,B_6)))
      | ~ v1_funct_2(C_7,A_5,B_6)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_163,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_159,c_6])).

tff(c_177,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_149,c_163])).

tff(c_203,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_356,plain,(
    ! [B_84,A_85,C_86] :
      ( k2_relset_1(u1_struct_0(B_84),u1_struct_0(A_85),k2_tops_2(u1_struct_0(A_85),u1_struct_0(B_84),C_86)) = k2_struct_0(A_85)
      | ~ v2_funct_1(C_86)
      | k2_relset_1(u1_struct_0(A_85),u1_struct_0(B_84),C_86) != k2_struct_0(B_84)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85),u1_struct_0(B_84))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_85),u1_struct_0(B_84))
      | ~ v1_funct_1(C_86)
      | ~ l1_struct_0(B_84)
      | v2_struct_0(B_84)
      | ~ l1_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_377,plain,(
    ! [A_85,C_86] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_85),k2_tops_2(u1_struct_0(A_85),u1_struct_0('#skF_2'),C_86)) = k2_struct_0(A_85)
      | ~ v2_funct_1(C_86)
      | k2_relset_1(u1_struct_0(A_85),u1_struct_0('#skF_2'),C_86) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_85),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_86)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_356])).

tff(c_398,plain,(
    ! [A_85,C_86] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_85),k2_tops_2(u1_struct_0(A_85),k2_struct_0('#skF_2'),C_86)) = k2_struct_0(A_85)
      | ~ v2_funct_1(C_86)
      | k2_relset_1(u1_struct_0(A_85),k2_struct_0('#skF_2'),C_86) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_85),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_86,u1_struct_0(A_85),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_86)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_52,c_52,c_52,c_377])).

tff(c_448,plain,(
    ! [A_94,C_95] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_94),k2_tops_2(u1_struct_0(A_94),k2_struct_0('#skF_2'),C_95)) = k2_struct_0(A_94)
      | ~ v2_funct_1(C_95)
      | k2_relset_1(u1_struct_0(A_94),k2_struct_0('#skF_2'),C_95) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_94),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_95,u1_struct_0(A_94),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_95)
      | ~ l1_struct_0(A_94) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_398])).

tff(c_457,plain,(
    ! [C_95] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_95)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_95)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_95) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_95,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_95)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_448])).

tff(c_477,plain,(
    ! [C_96] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_96)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_96)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_96) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_96,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_53,c_53,c_53,c_53,c_457])).

tff(c_486,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_477])).

tff(c_490,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_63,c_72,c_30,c_486])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_490])).

tff(c_493,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_499,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_493])).

tff(c_510,plain,(
    ! [A_98,B_99,C_100] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_98),u1_struct_0(B_99),C_100))
      | ~ v2_funct_1(C_100)
      | k2_relset_1(u1_struct_0(A_98),u1_struct_0(B_99),C_100) != k2_struct_0(B_99)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),u1_struct_0(B_99))))
      | ~ v1_funct_2(C_100,u1_struct_0(A_98),u1_struct_0(B_99))
      | ~ v1_funct_1(C_100)
      | ~ l1_struct_0(B_99)
      | ~ l1_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_526,plain,(
    ! [A_98,C_100] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_98),u1_struct_0('#skF_2'),C_100))
      | ~ v2_funct_1(C_100)
      | k2_relset_1(u1_struct_0(A_98),u1_struct_0('#skF_2'),C_100) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_98),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_100,u1_struct_0(A_98),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_100)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_510])).

tff(c_546,plain,(
    ! [A_102,C_103] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(A_102),k2_struct_0('#skF_2'),C_103))
      | ~ v2_funct_1(C_103)
      | k2_relset_1(u1_struct_0(A_102),k2_struct_0('#skF_2'),C_103) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_102),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_103,u1_struct_0(A_102),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_103)
      | ~ l1_struct_0(A_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52,c_52,c_52,c_526])).

tff(c_553,plain,(
    ! [C_103] :
      ( v2_funct_1(k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_103))
      | ~ v2_funct_1(C_103)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_103) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_103,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_103)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_546])).

tff(c_647,plain,(
    ! [C_114] :
      ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_114))
      | ~ v2_funct_1(C_114)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_114) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_114,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_53,c_53,c_53,c_553])).

tff(c_654,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_647])).

tff(c_658,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_72,c_30,c_147,c_654])).

tff(c_660,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_658])).

tff(c_661,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_493])).

tff(c_28,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_100,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_53,c_53,c_52,c_52,c_52,c_28])).

tff(c_151,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_100])).

tff(c_666,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_151])).

tff(c_678,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_666])).

tff(c_680,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_38,c_30,c_678])).

tff(c_189,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( r2_funct_2(A_57,B_58,C_59,C_59)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(D_60,A_57,B_58)
      | ~ v1_funct_1(D_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ v1_funct_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_195,plain,(
    ! [C_59] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_59,C_59)
      | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_59,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_63,c_189])).

tff(c_775,plain,(
    ! [C_118] :
      ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_118,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_118,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_195])).

tff(c_782,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_775])).

tff(c_789,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_64,c_782])).

tff(c_791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_680,c_789])).

%------------------------------------------------------------------------------
