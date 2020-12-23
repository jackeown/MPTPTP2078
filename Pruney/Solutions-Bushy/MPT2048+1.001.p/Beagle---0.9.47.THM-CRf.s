%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2048+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:48 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 155 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_yellow19 > v6_waybel_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_funct_1 > l1_struct_0 > k4_waybel_9 > k2_relset_1 > u1_waybel_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_yellow19,type,(
    m1_yellow19: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(A),u1_waybel_0(A,k4_waybel_9(A,B,C))),A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow19)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_yellow19(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                    & C = k2_relset_1(u1_struct_0(k4_waybel_9(A,B,D)),u1_struct_0(A),u1_waybel_0(A,k4_waybel_9(A,B,D))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow19)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_35,plain,(
    ! [A_44,B_45,C_46] :
      ( l1_waybel_0(k4_waybel_9(A_44,B_45,C_46),A_44)
      | ~ m1_subset_1(C_46,u1_struct_0(B_45))
      | ~ l1_waybel_0(B_45,A_44)
      | v2_struct_0(B_45)
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_37,plain,(
    ! [A_44] :
      ( l1_waybel_0(k4_waybel_9(A_44,'#skF_3','#skF_4'),A_44)
      | ~ l1_waybel_0('#skF_3',A_44)
      | v2_struct_0('#skF_3')
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_22,c_35])).

tff(c_40,plain,(
    ! [A_44] :
      ( l1_waybel_0(k4_waybel_9(A_44,'#skF_3','#skF_4'),A_44)
      | ~ l1_waybel_0('#skF_3',A_44)
      | ~ l1_struct_0(A_44)
      | v2_struct_0(A_44) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_37])).

tff(c_14,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(u1_waybel_0(A_29,B_30),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_30),u1_struct_0(A_29))))
      | ~ l1_waybel_0(B_30,A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_23,B_24,C_25] :
      ( m1_subset_1(k2_relset_1(A_23,B_24,C_25),k1_zfmisc_1(B_24))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_66,B_67,D_68] :
      ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(A_66,B_67,D_68)),u1_struct_0(A_66),u1_waybel_0(A_66,k4_waybel_9(A_66,B_67,D_68))),A_66,B_67)
      | ~ m1_subset_1(D_68,u1_struct_0(B_67))
      | ~ m1_subset_1(k2_relset_1(u1_struct_0(k4_waybel_9(A_66,B_67,D_68)),u1_struct_0(A_66),u1_waybel_0(A_66,k4_waybel_9(A_66,B_67,D_68))),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_waybel_0(B_67,A_66)
      | v2_struct_0(B_67)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_69,B_70,D_71] :
      ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(A_69,B_70,D_71)),u1_struct_0(A_69),u1_waybel_0(A_69,k4_waybel_9(A_69,B_70,D_71))),A_69,B_70)
      | ~ m1_subset_1(D_71,u1_struct_0(B_70))
      | ~ l1_waybel_0(B_70,A_69)
      | v2_struct_0(B_70)
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69)
      | ~ m1_subset_1(u1_waybel_0(A_69,k4_waybel_9(A_69,B_70,D_71)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_69,B_70,D_71)),u1_struct_0(A_69)))) ) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_80,plain,(
    ! [A_72,B_73,D_74] :
      ( m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9(A_72,B_73,D_74)),u1_struct_0(A_72),u1_waybel_0(A_72,k4_waybel_9(A_72,B_73,D_74))),A_72,B_73)
      | ~ m1_subset_1(D_74,u1_struct_0(B_73))
      | ~ l1_waybel_0(B_73,A_72)
      | v2_struct_0(B_73)
      | v2_struct_0(A_72)
      | ~ l1_waybel_0(k4_waybel_9(A_72,B_73,D_74),A_72)
      | ~ l1_struct_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_14,c_75])).

tff(c_20,plain,(
    ~ m1_yellow19(k2_relset_1(u1_struct_0(k4_waybel_9('#skF_2','#skF_3','#skF_4')),u1_struct_0('#skF_2'),u1_waybel_0('#skF_2',k4_waybel_9('#skF_2','#skF_3','#skF_4'))),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_83,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ l1_waybel_0(k4_waybel_9('#skF_2','#skF_3','#skF_4'),'#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_20])).

tff(c_89,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | ~ l1_waybel_0(k4_waybel_9('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_22,c_83])).

tff(c_90,plain,(
    ~ l1_waybel_0(k4_waybel_9('#skF_2','#skF_3','#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_26,c_89])).

tff(c_93,plain,
    ( ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_90])).

tff(c_96,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_93])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_96])).

%------------------------------------------------------------------------------
