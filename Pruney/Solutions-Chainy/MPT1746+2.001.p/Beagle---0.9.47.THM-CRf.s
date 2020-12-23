%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:49 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 233 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   10
%              Number of atoms          :  237 (1538 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( v1_funct_1(C)
                    & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                    & v5_pre_topc(C,A,B)
                    & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                <=> ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => r1_tmap_1(A,B,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tmap_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_56,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_61,plain,
    ( ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_56])).

tff(c_66,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_16,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_14,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_73,plain,(
    ! [A_43,B_44,C_45] :
      ( m1_subset_1('#skF_1'(A_43,B_44,C_45),u1_struct_0(B_44))
      | v5_pre_topc(C_45,B_44,A_43)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_44),u1_struct_0(A_43))))
      | ~ v1_funct_2(C_45,u1_struct_0(B_44),u1_struct_0(A_43))
      | ~ v1_funct_1(C_45)
      | ~ l1_pre_topc(B_44)
      | ~ v2_pre_topc(B_44)
      | v2_struct_0(B_44)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_78,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_22,c_20,c_12,c_10,c_75])).

tff(c_79,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_24,c_66,c_78])).

tff(c_44,plain,(
    ! [D_41] :
      ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | r1_tmap_1('#skF_2','#skF_3','#skF_4',D_41)
      | ~ m1_subset_1(D_41,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_67,plain,(
    ! [D_41] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_4',D_41)
      | ~ m1_subset_1(D_41,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_44])).

tff(c_83,plain,(
    r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_79,c_67])).

tff(c_84,plain,(
    ! [B_46,A_47,C_48] :
      ( ~ r1_tmap_1(B_46,A_47,C_48,'#skF_1'(A_47,B_46,C_48))
      | v5_pre_topc(C_48,B_46,A_47)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_46),u1_struct_0(A_47))))
      | ~ v1_funct_2(C_48,u1_struct_0(B_46),u1_struct_0(A_47))
      | ~ v1_funct_1(C_48)
      | ~ l1_pre_topc(B_46)
      | ~ v2_pre_topc(B_46)
      | v2_struct_0(B_46)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_86,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_84])).

tff(c_89,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_22,c_20,c_12,c_10,c_8,c_86])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_24,c_66,c_89])).

tff(c_92,plain,(
    ~ r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_93,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_40,plain,(
    ! [D_41] :
      ( m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | r1_tmap_1('#skF_2','#skF_3','#skF_4',D_41)
      | ~ m1_subset_1(D_41,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_103,plain,(
    ! [B_55,A_56,C_57,D_58] :
      ( r1_tmap_1(B_55,A_56,C_57,D_58)
      | ~ m1_subset_1(D_58,u1_struct_0(B_55))
      | ~ v5_pre_topc(C_57,B_55,A_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_55),u1_struct_0(A_56))))
      | ~ v1_funct_2(C_57,u1_struct_0(B_55),u1_struct_0(A_56))
      | ~ v1_funct_1(C_57)
      | ~ l1_pre_topc(B_55)
      | ~ v2_pre_topc(B_55)
      | v2_struct_0(B_55)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_105,plain,(
    ! [A_56,C_57] :
      ( r1_tmap_1('#skF_2',A_56,C_57,'#skF_5')
      | ~ v5_pre_topc(C_57,'#skF_2',A_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_56))))
      | ~ v1_funct_2(C_57,u1_struct_0('#skF_2'),u1_struct_0(A_56))
      | ~ v1_funct_1(C_57)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_64,c_103])).

tff(c_108,plain,(
    ! [A_56,C_57] :
      ( r1_tmap_1('#skF_2',A_56,C_57,'#skF_5')
      | ~ v5_pre_topc(C_57,'#skF_2',A_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_56))))
      | ~ v1_funct_2(C_57,u1_struct_0('#skF_2'),u1_struct_0(A_56))
      | ~ v1_funct_1(C_57)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_105])).

tff(c_110,plain,(
    ! [A_59,C_60] :
      ( r1_tmap_1('#skF_2',A_59,C_60,'#skF_5')
      | ~ v5_pre_topc(C_60,'#skF_2',A_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(A_59))))
      | ~ v1_funct_2(C_60,u1_struct_0('#skF_2'),u1_struct_0(A_59))
      | ~ v1_funct_1(C_60)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_108])).

tff(c_113,plain,
    ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_110])).

tff(c_116,plain,
    ( r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_10,c_93,c_113])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_92,c_116])).

tff(c_120,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_121,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_28,plain,
    ( m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_53,plain,
    ( m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_58,plain,
    ( m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_53])).

tff(c_63,plain,
    ( m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_123,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_63])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_123])).

tff(c_126,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_129,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1('#skF_1'(A_62,B_63,C_64),u1_struct_0(B_63))
      | v5_pre_topc(C_64,B_63,A_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_63),u1_struct_0(A_62))))
      | ~ v1_funct_2(C_64,u1_struct_0(B_63),u1_struct_0(A_62))
      | ~ v1_funct_1(C_64)
      | ~ l1_pre_topc(B_63)
      | ~ v2_pre_topc(B_63)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_131,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_129])).

tff(c_134,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_22,c_20,c_12,c_10,c_131])).

tff(c_135,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_24,c_126,c_134])).

tff(c_125,plain,(
    ! [D_41] :
      ( r1_tmap_1('#skF_2','#skF_3','#skF_4',D_41)
      | ~ m1_subset_1(D_41,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_139,plain,(
    r1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_135,c_125])).

tff(c_140,plain,(
    ! [B_65,A_66,C_67] :
      ( ~ r1_tmap_1(B_65,A_66,C_67,'#skF_1'(A_66,B_65,C_67))
      | v5_pre_topc(C_67,B_65,A_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_65),u1_struct_0(A_66))))
      | ~ v1_funct_2(C_67,u1_struct_0(B_65),u1_struct_0(A_66))
      | ~ v1_funct_1(C_67)
      | ~ l1_pre_topc(B_65)
      | ~ v2_pre_topc(B_65)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_142,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_139,c_140])).

tff(c_145,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_22,c_20,c_12,c_10,c_8,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_24,c_126,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:43:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.25  
% 2.41/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.25  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.41/1.25  
% 2.41/1.25  %Foreground sorts:
% 2.41/1.25  
% 2.41/1.25  
% 2.41/1.25  %Background operators:
% 2.41/1.25  
% 2.41/1.25  
% 2.41/1.25  %Foreground operators:
% 2.41/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.41/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.41/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.41/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.25  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.41/1.25  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.41/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.25  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.41/1.25  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.25  
% 2.41/1.27  tff(f_90, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => ((((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => r1_tmap_1(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tmap_1)).
% 2.41/1.27  tff(f_54, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 2.41/1.27  tff(c_18, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_24, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_8, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_10, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_12, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_26, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_50, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 2.41/1.27  tff(c_56, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50])).
% 2.41/1.27  tff(c_61, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_56])).
% 2.41/1.27  tff(c_66, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_61])).
% 2.41/1.27  tff(c_16, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_14, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_22, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_20, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_73, plain, (![A_43, B_44, C_45]: (m1_subset_1('#skF_1'(A_43, B_44, C_45), u1_struct_0(B_44)) | v5_pre_topc(C_45, B_44, A_43) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_44), u1_struct_0(A_43)))) | ~v1_funct_2(C_45, u1_struct_0(B_44), u1_struct_0(A_43)) | ~v1_funct_1(C_45) | ~l1_pre_topc(B_44) | ~v2_pre_topc(B_44) | v2_struct_0(B_44) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.27  tff(c_75, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_73])).
% 2.41/1.27  tff(c_78, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_22, c_20, c_12, c_10, c_75])).
% 2.41/1.27  tff(c_79, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_24, c_66, c_78])).
% 2.41/1.27  tff(c_44, plain, (![D_41]: (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | r1_tmap_1('#skF_2', '#skF_3', '#skF_4', D_41) | ~m1_subset_1(D_41, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_67, plain, (![D_41]: (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', D_41) | ~m1_subset_1(D_41, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_66, c_44])).
% 2.41/1.27  tff(c_83, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_79, c_67])).
% 2.41/1.27  tff(c_84, plain, (![B_46, A_47, C_48]: (~r1_tmap_1(B_46, A_47, C_48, '#skF_1'(A_47, B_46, C_48)) | v5_pre_topc(C_48, B_46, A_47) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_46), u1_struct_0(A_47)))) | ~v1_funct_2(C_48, u1_struct_0(B_46), u1_struct_0(A_47)) | ~v1_funct_1(C_48) | ~l1_pre_topc(B_46) | ~v2_pre_topc(B_46) | v2_struct_0(B_46) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.27  tff(c_86, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_83, c_84])).
% 2.41/1.27  tff(c_89, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_22, c_20, c_12, c_10, c_8, c_86])).
% 2.41/1.27  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_24, c_66, c_89])).
% 2.41/1.27  tff(c_92, plain, (~r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_61])).
% 2.41/1.27  tff(c_93, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_61])).
% 2.41/1.27  tff(c_40, plain, (![D_41]: (m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | r1_tmap_1('#skF_2', '#skF_3', '#skF_4', D_41) | ~m1_subset_1(D_41, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.41/1.27  tff(c_103, plain, (![B_55, A_56, C_57, D_58]: (r1_tmap_1(B_55, A_56, C_57, D_58) | ~m1_subset_1(D_58, u1_struct_0(B_55)) | ~v5_pre_topc(C_57, B_55, A_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_55), u1_struct_0(A_56)))) | ~v1_funct_2(C_57, u1_struct_0(B_55), u1_struct_0(A_56)) | ~v1_funct_1(C_57) | ~l1_pre_topc(B_55) | ~v2_pre_topc(B_55) | v2_struct_0(B_55) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.27  tff(c_105, plain, (![A_56, C_57]: (r1_tmap_1('#skF_2', A_56, C_57, '#skF_5') | ~v5_pre_topc(C_57, '#skF_2', A_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_56)))) | ~v1_funct_2(C_57, u1_struct_0('#skF_2'), u1_struct_0(A_56)) | ~v1_funct_1(C_57) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_64, c_103])).
% 2.41/1.27  tff(c_108, plain, (![A_56, C_57]: (r1_tmap_1('#skF_2', A_56, C_57, '#skF_5') | ~v5_pre_topc(C_57, '#skF_2', A_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_56)))) | ~v1_funct_2(C_57, u1_struct_0('#skF_2'), u1_struct_0(A_56)) | ~v1_funct_1(C_57) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_105])).
% 2.41/1.27  tff(c_110, plain, (![A_59, C_60]: (r1_tmap_1('#skF_2', A_59, C_60, '#skF_5') | ~v5_pre_topc(C_60, '#skF_2', A_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(A_59)))) | ~v1_funct_2(C_60, u1_struct_0('#skF_2'), u1_struct_0(A_59)) | ~v1_funct_1(C_60) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(negUnitSimplification, [status(thm)], [c_24, c_108])).
% 2.41/1.27  tff(c_113, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_110])).
% 2.41/1.27  tff(c_116, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_10, c_93, c_113])).
% 2.41/1.27  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_92, c_116])).
% 2.41/1.27  tff(c_120, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_40])).
% 2.41/1.27  tff(c_121, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_44])).
% 2.41/1.27  tff(c_28, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.41/1.27  tff(c_53, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 2.41/1.27  tff(c_58, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_53])).
% 2.41/1.27  tff(c_63, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_58])).
% 2.41/1.27  tff(c_123, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_63])).
% 2.41/1.27  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120, c_123])).
% 2.41/1.27  tff(c_126, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 2.41/1.27  tff(c_129, plain, (![A_62, B_63, C_64]: (m1_subset_1('#skF_1'(A_62, B_63, C_64), u1_struct_0(B_63)) | v5_pre_topc(C_64, B_63, A_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_63), u1_struct_0(A_62)))) | ~v1_funct_2(C_64, u1_struct_0(B_63), u1_struct_0(A_62)) | ~v1_funct_1(C_64) | ~l1_pre_topc(B_63) | ~v2_pre_topc(B_63) | v2_struct_0(B_63) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.27  tff(c_131, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_129])).
% 2.41/1.27  tff(c_134, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_22, c_20, c_12, c_10, c_131])).
% 2.41/1.27  tff(c_135, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_24, c_126, c_134])).
% 2.41/1.27  tff(c_125, plain, (![D_41]: (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', D_41) | ~m1_subset_1(D_41, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_44])).
% 2.41/1.27  tff(c_139, plain, (r1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_135, c_125])).
% 2.41/1.27  tff(c_140, plain, (![B_65, A_66, C_67]: (~r1_tmap_1(B_65, A_66, C_67, '#skF_1'(A_66, B_65, C_67)) | v5_pre_topc(C_67, B_65, A_66) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_65), u1_struct_0(A_66)))) | ~v1_funct_2(C_67, u1_struct_0(B_65), u1_struct_0(A_66)) | ~v1_funct_1(C_67) | ~l1_pre_topc(B_65) | ~v2_pre_topc(B_65) | v2_struct_0(B_65) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.27  tff(c_142, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_139, c_140])).
% 2.41/1.27  tff(c_145, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_22, c_20, c_12, c_10, c_8, c_142])).
% 2.41/1.27  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_24, c_126, c_145])).
% 2.41/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.27  
% 2.41/1.27  Inference rules
% 2.41/1.27  ----------------------
% 2.41/1.27  #Ref     : 0
% 2.41/1.27  #Sup     : 10
% 2.41/1.27  #Fact    : 0
% 2.41/1.27  #Define  : 0
% 2.41/1.27  #Split   : 3
% 2.41/1.27  #Chain   : 0
% 2.41/1.27  #Close   : 0
% 2.41/1.27  
% 2.41/1.27  Ordering : KBO
% 2.41/1.27  
% 2.41/1.27  Simplification rules
% 2.41/1.27  ----------------------
% 2.41/1.27  #Subsume      : 6
% 2.41/1.27  #Demod        : 52
% 2.41/1.27  #Tautology    : 10
% 2.41/1.27  #SimpNegUnit  : 10
% 2.41/1.27  #BackRed      : 0
% 2.41/1.27  
% 2.41/1.27  #Partial instantiations: 0
% 2.41/1.27  #Strategies tried      : 1
% 2.41/1.27  
% 2.41/1.27  Timing (in seconds)
% 2.41/1.27  ----------------------
% 2.41/1.27  Preprocessing        : 0.30
% 2.41/1.27  Parsing              : 0.16
% 2.41/1.27  CNF conversion       : 0.03
% 2.41/1.27  Main loop            : 0.20
% 2.41/1.27  Inferencing          : 0.08
% 2.41/1.28  Reduction            : 0.06
% 2.41/1.28  Demodulation         : 0.05
% 2.41/1.28  BG Simplification    : 0.01
% 2.41/1.28  Subsumption          : 0.03
% 2.41/1.28  Abstraction          : 0.01
% 2.41/1.28  MUC search           : 0.00
% 2.41/1.28  Cooper               : 0.00
% 2.41/1.28  Total                : 0.54
% 2.41/1.28  Index Insertion      : 0.00
% 2.41/1.28  Index Deletion       : 0.00
% 2.41/1.28  Index Matching       : 0.00
% 2.41/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
