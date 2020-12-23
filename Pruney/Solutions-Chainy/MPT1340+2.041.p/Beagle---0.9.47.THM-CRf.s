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
% DateTime   : Thu Dec  3 10:23:35 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   93 (1085 expanded)
%              Number of leaves         :   31 ( 417 expanded)
%              Depth                    :   12
%              Number of atoms          :  259 (3697 expanded)
%              Number of equality atoms :   59 ( 785 expanded)
%              Maximal formula depth    :   14 (   5 average)
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

tff(f_142,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(f_120,axiom,(
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

tff(c_46,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_47,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_47])).

tff(c_42,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_36])).

tff(c_72,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_72])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_38,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_38])).

tff(c_70,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_56])).

tff(c_107,plain,(
    ! [A_36,B_37,D_38] :
      ( r2_funct_2(A_36,B_37,D_38,D_38)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(D_38,A_36,B_37)
      | ~ v1_funct_1(D_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_109,plain,
    ( r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_107])).

tff(c_112,plain,(
    r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_109])).

tff(c_8,plain,(
    ! [A_2] :
      ( k2_funct_1(k2_funct_1(A_2)) = A_2
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_65,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_54,c_34])).

tff(c_113,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_funct_1(k2_funct_1(C_39))
      | k2_relset_1(A_40,B_41,C_39) != B_41
      | ~ v2_funct_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_2(C_39,A_40,B_41)
      | ~ v1_funct_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_116,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_113])).

tff(c_119,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_32,c_65,c_116])).

tff(c_120,plain,(
    ! [C_42,B_43,A_44] :
      ( v1_funct_2(k2_funct_1(C_42),B_43,A_44)
      | k2_relset_1(A_44,B_43,C_42) != B_43
      | ~ v2_funct_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43)))
      | ~ v1_funct_2(C_42,A_44,B_43)
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_123,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_120])).

tff(c_126,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_32,c_65,c_123])).

tff(c_2,plain,(
    ! [A_1] :
      ( v2_funct_1(k2_funct_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,(
    ! [C_48,B_49,A_50] :
      ( m1_subset_1(k2_funct_1(C_48),k1_zfmisc_1(k2_zfmisc_1(B_49,A_50)))
      | k2_relset_1(A_50,B_49,C_48) != B_49
      | ~ v2_funct_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49)))
      | ~ v1_funct_2(C_48,A_50,B_49)
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [C_12,A_10,B_11] :
      ( v1_funct_1(k2_funct_1(C_12))
      | k2_relset_1(A_10,B_11,C_12) != B_11
      | ~ v2_funct_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(C_12,A_10,B_11)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_199,plain,(
    ! [C_64,B_65,A_66] :
      ( v1_funct_1(k2_funct_1(k2_funct_1(C_64)))
      | k2_relset_1(B_65,A_66,k2_funct_1(C_64)) != A_66
      | ~ v2_funct_1(k2_funct_1(C_64))
      | ~ v1_funct_2(k2_funct_1(C_64),B_65,A_66)
      | ~ v1_funct_1(k2_funct_1(C_64))
      | k2_relset_1(A_66,B_65,C_64) != B_65
      | ~ v2_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65)))
      | ~ v1_funct_2(C_64,A_66,B_65)
      | ~ v1_funct_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_139,c_20])).

tff(c_205,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_199])).

tff(c_209,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_32,c_65,c_119,c_126,c_205])).

tff(c_261,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_264,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_261])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40,c_32,c_264])).

tff(c_269,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_300,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_127,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_tops_2(A_45,B_46,C_47) = k2_funct_1(C_47)
      | ~ v2_funct_1(C_47)
      | k2_relset_1(A_45,B_46,C_47) != B_46
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_130,plain,
    ( k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_127])).

tff(c_133,plain,(
    k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_65,c_32,c_130])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_210,plain,(
    ! [B_67,A_68,C_69] :
      ( k2_relset_1(u1_struct_0(B_67),u1_struct_0(A_68),k2_tops_2(u1_struct_0(A_68),u1_struct_0(B_67),C_69)) = k2_struct_0(A_68)
      | ~ v2_funct_1(C_69)
      | k2_relset_1(u1_struct_0(A_68),u1_struct_0(B_67),C_69) != k2_struct_0(B_67)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0(B_67))))
      | ~ v1_funct_2(C_69,u1_struct_0(A_68),u1_struct_0(B_67))
      | ~ v1_funct_1(C_69)
      | ~ l1_struct_0(B_67)
      | v2_struct_0(B_67)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_240,plain,(
    ! [A_68,C_69] :
      ( k2_relset_1(u1_struct_0('#skF_2'),u1_struct_0(A_68),k2_tops_2(u1_struct_0(A_68),k2_struct_0('#skF_2'),C_69)) = k2_struct_0(A_68)
      | ~ v2_funct_1(C_69)
      | k2_relset_1(u1_struct_0(A_68),u1_struct_0('#skF_2'),C_69) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_69,u1_struct_0(A_68),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_69)
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_210])).

tff(c_259,plain,(
    ! [A_68,C_69] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_68),k2_tops_2(u1_struct_0(A_68),k2_struct_0('#skF_2'),C_69)) = k2_struct_0(A_68)
      | ~ v2_funct_1(C_69)
      | k2_relset_1(u1_struct_0(A_68),k2_struct_0('#skF_2'),C_69) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_69,u1_struct_0(A_68),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_69)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54,c_54,c_54,c_54,c_240])).

tff(c_271,plain,(
    ! [A_70,C_71] :
      ( k2_relset_1(k2_struct_0('#skF_2'),u1_struct_0(A_70),k2_tops_2(u1_struct_0(A_70),k2_struct_0('#skF_2'),C_71)) = k2_struct_0(A_70)
      | ~ v2_funct_1(C_71)
      | k2_relset_1(u1_struct_0(A_70),k2_struct_0('#skF_2'),C_71) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_71,u1_struct_0(A_70),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_71)
      | ~ l1_struct_0(A_70) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_259])).

tff(c_280,plain,(
    ! [C_71] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_71)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_71)
      | k2_relset_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_71) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_71,u1_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_71)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_271])).

tff(c_301,plain,(
    ! [C_72] :
      ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_72)) = k2_struct_0('#skF_1')
      | ~ v2_funct_1(C_72)
      | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),C_72) != k2_struct_0('#skF_2')
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_72,k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_55,c_55,c_55,c_55,c_280])).

tff(c_310,plain,
    ( k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_301])).

tff(c_314,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_71,c_65,c_32,c_310])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_314])).

tff(c_318,plain,(
    k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_270,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_24,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_tops_2(A_14,B_15,C_16) = k2_funct_1(C_16)
      | ~ v2_funct_1(C_16)
      | k2_relset_1(A_14,B_15,C_16) != B_15
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_514,plain,(
    ! [B_90,A_91,C_92] :
      ( k2_tops_2(B_90,A_91,k2_funct_1(C_92)) = k2_funct_1(k2_funct_1(C_92))
      | ~ v2_funct_1(k2_funct_1(C_92))
      | k2_relset_1(B_90,A_91,k2_funct_1(C_92)) != A_91
      | ~ v1_funct_2(k2_funct_1(C_92),B_90,A_91)
      | ~ v1_funct_1(k2_funct_1(C_92))
      | k2_relset_1(A_91,B_90,C_92) != B_90
      | ~ v2_funct_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_91,B_90)))
      | ~ v1_funct_2(C_92,A_91,B_90)
      | ~ v1_funct_1(C_92) ) ),
    inference(resolution,[status(thm)],[c_139,c_24])).

tff(c_520,plain,
    ( k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) != k2_struct_0('#skF_1')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_struct_0('#skF_2'),k2_struct_0('#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_514])).

tff(c_524,plain,(
    k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_70,c_32,c_65,c_119,c_126,c_318,c_270,c_520])).

tff(c_30,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_106,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_55,c_55,c_54,c_54,c_54,c_30])).

tff(c_134,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_106])).

tff(c_525,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_134])).

tff(c_532,plain,
    ( ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_525])).

tff(c_535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40,c_32,c_112,c_532])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:11:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.51  
% 3.41/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.51  %$ r2_funct_2 > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_funct_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.41/1.51  
% 3.41/1.51  %Foreground sorts:
% 3.41/1.51  
% 3.41/1.51  
% 3.41/1.51  %Background operators:
% 3.41/1.51  
% 3.41/1.51  
% 3.41/1.51  %Foreground operators:
% 3.41/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.41/1.51  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.41/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.41/1.51  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.41/1.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.41/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.51  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 3.41/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.41/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.41/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.41/1.51  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.41/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.41/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.51  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.41/1.51  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.41/1.51  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 3.41/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.41/1.51  
% 3.53/1.54  tff(f_142, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 3.53/1.54  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.53/1.54  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.53/1.54  tff(f_65, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 3.53/1.54  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 3.53/1.54  tff(f_81, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 3.53/1.54  tff(f_37, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.53/1.54  tff(f_97, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 3.53/1.54  tff(f_120, axiom, (![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => ((k1_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(B)) & (k2_relset_1(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)) = k2_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_tops_2)).
% 3.53/1.54  tff(c_46, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_47, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_55, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_47])).
% 3.53/1.54  tff(c_42, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_54, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_47])).
% 3.53/1.54  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_36])).
% 3.53/1.54  tff(c_72, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.53/1.54  tff(c_76, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_72])).
% 3.53/1.54  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_38, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_56, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_38])).
% 3.53/1.54  tff(c_70, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_56])).
% 3.53/1.54  tff(c_107, plain, (![A_36, B_37, D_38]: (r2_funct_2(A_36, B_37, D_38, D_38) | ~m1_subset_1(D_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(D_38, A_36, B_37) | ~v1_funct_1(D_38))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.54  tff(c_109, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_107])).
% 3.53/1.54  tff(c_112, plain, (r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_109])).
% 3.53/1.54  tff(c_8, plain, (![A_2]: (k2_funct_1(k2_funct_1(A_2))=A_2 | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.54  tff(c_34, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_65, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_54, c_34])).
% 3.53/1.54  tff(c_113, plain, (![C_39, A_40, B_41]: (v1_funct_1(k2_funct_1(C_39)) | k2_relset_1(A_40, B_41, C_39)!=B_41 | ~v2_funct_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_2(C_39, A_40, B_41) | ~v1_funct_1(C_39))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.53/1.54  tff(c_116, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_113])).
% 3.53/1.54  tff(c_119, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_32, c_65, c_116])).
% 3.53/1.54  tff(c_120, plain, (![C_42, B_43, A_44]: (v1_funct_2(k2_funct_1(C_42), B_43, A_44) | k2_relset_1(A_44, B_43, C_42)!=B_43 | ~v2_funct_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))) | ~v1_funct_2(C_42, A_44, B_43) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.53/1.54  tff(c_123, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_120])).
% 3.53/1.54  tff(c_126, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_32, c_65, c_123])).
% 3.53/1.54  tff(c_2, plain, (![A_1]: (v2_funct_1(k2_funct_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.53/1.54  tff(c_139, plain, (![C_48, B_49, A_50]: (m1_subset_1(k2_funct_1(C_48), k1_zfmisc_1(k2_zfmisc_1(B_49, A_50))) | k2_relset_1(A_50, B_49, C_48)!=B_49 | ~v2_funct_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))) | ~v1_funct_2(C_48, A_50, B_49) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.53/1.54  tff(c_20, plain, (![C_12, A_10, B_11]: (v1_funct_1(k2_funct_1(C_12)) | k2_relset_1(A_10, B_11, C_12)!=B_11 | ~v2_funct_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(C_12, A_10, B_11) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.53/1.54  tff(c_199, plain, (![C_64, B_65, A_66]: (v1_funct_1(k2_funct_1(k2_funct_1(C_64))) | k2_relset_1(B_65, A_66, k2_funct_1(C_64))!=A_66 | ~v2_funct_1(k2_funct_1(C_64)) | ~v1_funct_2(k2_funct_1(C_64), B_65, A_66) | ~v1_funct_1(k2_funct_1(C_64)) | k2_relset_1(A_66, B_65, C_64)!=B_65 | ~v2_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))) | ~v1_funct_2(C_64, A_66, B_65) | ~v1_funct_1(C_64))), inference(resolution, [status(thm)], [c_139, c_20])).
% 3.53/1.54  tff(c_205, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_199])).
% 3.53/1.54  tff(c_209, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_32, c_65, c_119, c_126, c_205])).
% 3.53/1.54  tff(c_261, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_209])).
% 3.53/1.54  tff(c_264, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2, c_261])).
% 3.53/1.54  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_40, c_32, c_264])).
% 3.53/1.54  tff(c_269, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_209])).
% 3.53/1.54  tff(c_300, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_269])).
% 3.53/1.54  tff(c_127, plain, (![A_45, B_46, C_47]: (k2_tops_2(A_45, B_46, C_47)=k2_funct_1(C_47) | ~v2_funct_1(C_47) | k2_relset_1(A_45, B_46, C_47)!=B_46 | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_2(C_47, A_45, B_46) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.54  tff(c_130, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_127])).
% 3.53/1.54  tff(c_133, plain, (k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_65, c_32, c_130])).
% 3.53/1.54  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_210, plain, (![B_67, A_68, C_69]: (k2_relset_1(u1_struct_0(B_67), u1_struct_0(A_68), k2_tops_2(u1_struct_0(A_68), u1_struct_0(B_67), C_69))=k2_struct_0(A_68) | ~v2_funct_1(C_69) | k2_relset_1(u1_struct_0(A_68), u1_struct_0(B_67), C_69)!=k2_struct_0(B_67) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0(B_67)))) | ~v1_funct_2(C_69, u1_struct_0(A_68), u1_struct_0(B_67)) | ~v1_funct_1(C_69) | ~l1_struct_0(B_67) | v2_struct_0(B_67) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.53/1.54  tff(c_240, plain, (![A_68, C_69]: (k2_relset_1(u1_struct_0('#skF_2'), u1_struct_0(A_68), k2_tops_2(u1_struct_0(A_68), k2_struct_0('#skF_2'), C_69))=k2_struct_0(A_68) | ~v2_funct_1(C_69) | k2_relset_1(u1_struct_0(A_68), u1_struct_0('#skF_2'), C_69)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), u1_struct_0('#skF_2')))) | ~v1_funct_2(C_69, u1_struct_0(A_68), u1_struct_0('#skF_2')) | ~v1_funct_1(C_69) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0(A_68))), inference(superposition, [status(thm), theory('equality')], [c_54, c_210])).
% 3.53/1.54  tff(c_259, plain, (![A_68, C_69]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_68), k2_tops_2(u1_struct_0(A_68), k2_struct_0('#skF_2'), C_69))=k2_struct_0(A_68) | ~v2_funct_1(C_69) | k2_relset_1(u1_struct_0(A_68), k2_struct_0('#skF_2'), C_69)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_68), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_69, u1_struct_0(A_68), k2_struct_0('#skF_2')) | ~v1_funct_1(C_69) | v2_struct_0('#skF_2') | ~l1_struct_0(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54, c_54, c_54, c_54, c_240])).
% 3.53/1.54  tff(c_271, plain, (![A_70, C_71]: (k2_relset_1(k2_struct_0('#skF_2'), u1_struct_0(A_70), k2_tops_2(u1_struct_0(A_70), k2_struct_0('#skF_2'), C_71))=k2_struct_0(A_70) | ~v2_funct_1(C_71) | k2_relset_1(u1_struct_0(A_70), k2_struct_0('#skF_2'), C_71)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_71, u1_struct_0(A_70), k2_struct_0('#skF_2')) | ~v1_funct_1(C_71) | ~l1_struct_0(A_70))), inference(negUnitSimplification, [status(thm)], [c_44, c_259])).
% 3.53/1.54  tff(c_280, plain, (![C_71]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_71))=k2_struct_0('#skF_1') | ~v2_funct_1(C_71) | k2_relset_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_71)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_71, u1_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_71) | ~l1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_55, c_271])).
% 3.53/1.54  tff(c_301, plain, (![C_72]: (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_72))=k2_struct_0('#skF_1') | ~v2_funct_1(C_72) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), C_72)!=k2_struct_0('#skF_2') | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_72, k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_72))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_55, c_55, c_55, c_55, c_280])).
% 3.53/1.54  tff(c_310, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1') | ~v2_funct_1('#skF_3') | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2')))) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_301])).
% 3.53/1.54  tff(c_314, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_71, c_65, c_32, c_310])).
% 3.53/1.54  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_300, c_314])).
% 3.53/1.54  tff(c_318, plain, (k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_269])).
% 3.53/1.54  tff(c_270, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_209])).
% 3.53/1.54  tff(c_24, plain, (![A_14, B_15, C_16]: (k2_tops_2(A_14, B_15, C_16)=k2_funct_1(C_16) | ~v2_funct_1(C_16) | k2_relset_1(A_14, B_15, C_16)!=B_15 | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.54  tff(c_514, plain, (![B_90, A_91, C_92]: (k2_tops_2(B_90, A_91, k2_funct_1(C_92))=k2_funct_1(k2_funct_1(C_92)) | ~v2_funct_1(k2_funct_1(C_92)) | k2_relset_1(B_90, A_91, k2_funct_1(C_92))!=A_91 | ~v1_funct_2(k2_funct_1(C_92), B_90, A_91) | ~v1_funct_1(k2_funct_1(C_92)) | k2_relset_1(A_91, B_90, C_92)!=B_90 | ~v2_funct_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_91, B_90))) | ~v1_funct_2(C_92, A_91, B_90) | ~v1_funct_1(C_92))), inference(resolution, [status(thm)], [c_139, c_24])).
% 3.53/1.54  tff(c_520, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))!=k2_struct_0('#skF_1') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_struct_0('#skF_2'), k2_struct_0('#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_514])).
% 3.53/1.54  tff(c_524, plain, (k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_70, c_32, c_65, c_119, c_126, c_318, c_270, c_520])).
% 3.53/1.54  tff(c_30, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.53/1.54  tff(c_106, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_55, c_55, c_54, c_54, c_54, c_30])).
% 3.53/1.54  tff(c_134, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_106])).
% 3.53/1.54  tff(c_525, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_134])).
% 3.53/1.54  tff(c_532, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_525])).
% 3.53/1.54  tff(c_535, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_40, c_32, c_112, c_532])).
% 3.53/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.54  
% 3.53/1.54  Inference rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Ref     : 0
% 3.53/1.54  #Sup     : 105
% 3.53/1.54  #Fact    : 0
% 3.53/1.54  #Define  : 0
% 3.53/1.54  #Split   : 3
% 3.53/1.54  #Chain   : 0
% 3.53/1.54  #Close   : 0
% 3.53/1.54  
% 3.53/1.54  Ordering : KBO
% 3.53/1.54  
% 3.53/1.54  Simplification rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Subsume      : 8
% 3.53/1.54  #Demod        : 229
% 3.53/1.54  #Tautology    : 50
% 3.53/1.54  #SimpNegUnit  : 7
% 3.53/1.54  #BackRed      : 3
% 3.53/1.54  
% 3.53/1.54  #Partial instantiations: 0
% 3.53/1.54  #Strategies tried      : 1
% 3.53/1.54  
% 3.53/1.54  Timing (in seconds)
% 3.53/1.54  ----------------------
% 3.53/1.54  Preprocessing        : 0.35
% 3.53/1.54  Parsing              : 0.18
% 3.53/1.54  CNF conversion       : 0.03
% 3.53/1.54  Main loop            : 0.40
% 3.53/1.54  Inferencing          : 0.14
% 3.53/1.54  Reduction            : 0.14
% 3.53/1.54  Demodulation         : 0.10
% 3.53/1.54  BG Simplification    : 0.03
% 3.53/1.54  Subsumption          : 0.07
% 3.53/1.54  Abstraction          : 0.02
% 3.53/1.54  MUC search           : 0.00
% 3.53/1.54  Cooper               : 0.00
% 3.53/1.54  Total                : 0.80
% 3.53/1.54  Index Insertion      : 0.00
% 3.53/1.54  Index Deletion       : 0.00
% 3.53/1.54  Index Matching       : 0.00
% 3.53/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
