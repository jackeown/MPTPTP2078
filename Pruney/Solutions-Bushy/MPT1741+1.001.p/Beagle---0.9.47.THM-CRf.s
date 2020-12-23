%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:20 EST 2020

% Result     : Theorem 13.41s
% Output     : CNFRefutation 13.71s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 896 expanded)
%              Number of leaves         :   37 ( 361 expanded)
%              Depth                    :   25
%              Number of atoms          : 1184 (8248 expanded)
%              Number of equality atoms :   11 ( 367 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_174,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( ( u1_struct_0(B) = u1_struct_0(C)
                    & r1_tarski(u1_pre_topc(C),u1_pre_topc(B)) )
                 => ! [D] :
                      ( ( v1_funct_1(D)
                        & v1_funct_2(D,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(A),u1_struct_0(C))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                         => ( r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),D,E)
                           => ! [F] :
                                ( m1_subset_1(F,u1_struct_0(A))
                               => ( r1_tmap_1(A,B,D,F)
                                 => r1_tmap_1(A,C,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tmap_1)).

tff(f_110,axiom,(
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
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_tmap_1(A,B,C,D)
                  <=> ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ~ ( v3_pre_topc(E,B)
                            & r2_hidden(k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,D),E)
                            & ! [F] :
                                ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(A)))
                               => ~ ( v3_pre_topc(F,A)
                                    & r2_hidden(D,F)
                                    & r1_tarski(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,F),E) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tmap_1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_36,plain,(
    ~ r1_tmap_1('#skF_3','#skF_5','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_74,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_72,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_62,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_60,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_58,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_46,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_77,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_46])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_44])).

tff(c_18,plain,(
    ! [A_14,B_70,C_98,D_112] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0(B_70),C_98,D_112),'#skF_2'(A_14,B_70,C_98,D_112))
      | r1_tmap_1(A_14,B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_42,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),'#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_79,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_42])).

tff(c_1057,plain,(
    ! [F_391,D_393,A_395,E_394,C_392,B_390] :
      ( F_391 = E_394
      | ~ r1_funct_2(A_395,B_390,C_392,D_393,E_394,F_391)
      | ~ m1_subset_1(F_391,k1_zfmisc_1(k2_zfmisc_1(C_392,D_393)))
      | ~ v1_funct_2(F_391,C_392,D_393)
      | ~ v1_funct_1(F_391)
      | ~ m1_subset_1(E_394,k1_zfmisc_1(k2_zfmisc_1(A_395,B_390)))
      | ~ v1_funct_2(E_394,A_395,B_390)
      | ~ v1_funct_1(E_394)
      | v1_xboole_0(D_393)
      | v1_xboole_0(B_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1059,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_79,c_1057])).

tff(c_1062,plain,
    ( '#skF_7' = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_77,c_78,c_1059])).

tff(c_1063,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_1121,plain,(
    ! [A_412,B_413,C_414,D_415] :
      ( m1_subset_1('#skF_2'(A_412,B_413,C_414,D_415),k1_zfmisc_1(u1_struct_0(B_413)))
      | r1_tmap_1(A_412,B_413,C_414,D_415)
      | ~ m1_subset_1(D_415,u1_struct_0(A_412))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0(A_412),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_pre_topc(B_413)
      | ~ v2_pre_topc(B_413)
      | v2_struct_0(B_413)
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1132,plain,(
    ! [A_412,C_414,D_415] :
      ( m1_subset_1('#skF_2'(A_412,'#skF_5',C_414,D_415),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1(A_412,'#skF_5',C_414,D_415)
      | ~ m1_subset_1(D_415,u1_struct_0(A_412))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_414,u1_struct_0(A_412),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_414)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1121])).

tff(c_1146,plain,(
    ! [A_412,C_414,D_415] :
      ( m1_subset_1('#skF_2'(A_412,'#skF_5',C_414,D_415),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_412,'#skF_5',C_414,D_415)
      | ~ m1_subset_1(D_415,u1_struct_0(A_412))
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_414,u1_struct_0(A_412),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_414)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_58,c_1132])).

tff(c_1464,plain,(
    ! [A_475,C_476,D_477] :
      ( m1_subset_1('#skF_2'(A_475,'#skF_5',C_476,D_477),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_475,'#skF_5',C_476,D_477)
      | ~ m1_subset_1(D_477,u1_struct_0(A_475))
      | ~ m1_subset_1(C_476,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_475),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_476,u1_struct_0(A_475),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_476)
      | ~ l1_pre_topc(A_475)
      | ~ v2_pre_topc(A_475)
      | v2_struct_0(A_475) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1146])).

tff(c_1466,plain,(
    ! [D_477] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_7',D_477),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_477)
      | ~ m1_subset_1(D_477,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_1464])).

tff(c_1476,plain,(
    ! [D_477] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_7',D_477),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_477)
      | ~ m1_subset_1(D_477,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_48,c_77,c_1466])).

tff(c_1486,plain,(
    ! [D_478] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_7',D_478),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_478)
      | ~ m1_subset_1(D_478,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1476])).

tff(c_34,plain,(
    ! [C_128,B_127,A_126] :
      ( ~ v1_xboole_0(C_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(C_128))
      | ~ r2_hidden(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1502,plain,(
    ! [A_126,D_478] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_126,'#skF_2'('#skF_3','#skF_5','#skF_7',D_478))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_478)
      | ~ m1_subset_1(D_478,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1486,c_34])).

tff(c_1552,plain,(
    ! [A_480,D_481] :
      ( ~ r2_hidden(A_480,'#skF_2'('#skF_3','#skF_5','#skF_7',D_481))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_481)
      | ~ m1_subset_1(D_481,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1502])).

tff(c_1556,plain,(
    ! [D_112] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_7',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_1552])).

tff(c_1563,plain,(
    ! [D_112] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_7',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_60,c_48,c_77,c_58,c_78,c_58,c_1556])).

tff(c_1566,plain,(
    ! [D_482] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_7',D_482)
      | ~ m1_subset_1(D_482,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64,c_1563])).

tff(c_1569,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_1566])).

tff(c_1573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1569])).

tff(c_1574,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_1582,plain,(
    ~ r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_36])).

tff(c_38,plain,(
    r1_tmap_1('#skF_3','#skF_4','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1593,plain,(
    ! [A_483,B_484,C_485,D_486] :
      ( v3_pre_topc('#skF_2'(A_483,B_484,C_485,D_486),B_484)
      | r1_tmap_1(A_483,B_484,C_485,D_486)
      | ~ m1_subset_1(D_486,u1_struct_0(A_483))
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_483),u1_struct_0(B_484))))
      | ~ v1_funct_2(C_485,u1_struct_0(A_483),u1_struct_0(B_484))
      | ~ v1_funct_1(C_485)
      | ~ l1_pre_topc(B_484)
      | ~ v2_pre_topc(B_484)
      | v2_struct_0(B_484)
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1602,plain,(
    ! [A_483,C_485,D_486] :
      ( v3_pre_topc('#skF_2'(A_483,'#skF_5',C_485,D_486),'#skF_5')
      | r1_tmap_1(A_483,'#skF_5',C_485,D_486)
      | ~ m1_subset_1(D_486,u1_struct_0(A_483))
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_483),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_485,u1_struct_0(A_483),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_485)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1593])).

tff(c_1612,plain,(
    ! [A_483,C_485,D_486] :
      ( v3_pre_topc('#skF_2'(A_483,'#skF_5',C_485,D_486),'#skF_5')
      | r1_tmap_1(A_483,'#skF_5',C_485,D_486)
      | ~ m1_subset_1(D_486,u1_struct_0(A_483))
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_483),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_485,u1_struct_0(A_483),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_485)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1602])).

tff(c_1632,plain,(
    ! [A_490,C_491,D_492] :
      ( v3_pre_topc('#skF_2'(A_490,'#skF_5',C_491,D_492),'#skF_5')
      | r1_tmap_1(A_490,'#skF_5',C_491,D_492)
      | ~ m1_subset_1(D_492,u1_struct_0(A_490))
      | ~ m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_491,u1_struct_0(A_490),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_491)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1612])).

tff(c_1637,plain,(
    ! [D_492] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_492),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_492)
      | ~ m1_subset_1(D_492,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1632])).

tff(c_1643,plain,(
    ! [D_492] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_492),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_492)
      | ~ m1_subset_1(D_492,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_1637])).

tff(c_1644,plain,(
    ! [D_492] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_492),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_492)
      | ~ m1_subset_1(D_492,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1643])).

tff(c_1676,plain,(
    ! [A_506,B_507,C_508,D_509] :
      ( m1_subset_1('#skF_2'(A_506,B_507,C_508,D_509),k1_zfmisc_1(u1_struct_0(B_507)))
      | r1_tmap_1(A_506,B_507,C_508,D_509)
      | ~ m1_subset_1(D_509,u1_struct_0(A_506))
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_506),u1_struct_0(B_507))))
      | ~ v1_funct_2(C_508,u1_struct_0(A_506),u1_struct_0(B_507))
      | ~ v1_funct_1(C_508)
      | ~ l1_pre_topc(B_507)
      | ~ v2_pre_topc(B_507)
      | v2_struct_0(B_507)
      | ~ l1_pre_topc(A_506)
      | ~ v2_pre_topc(A_506)
      | v2_struct_0(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1685,plain,(
    ! [A_506,C_508,D_509] :
      ( m1_subset_1('#skF_2'(A_506,'#skF_5',C_508,D_509),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1(A_506,'#skF_5',C_508,D_509)
      | ~ m1_subset_1(D_509,u1_struct_0(A_506))
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_506),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_508,u1_struct_0(A_506),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_508)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_506)
      | ~ v2_pre_topc(A_506)
      | v2_struct_0(A_506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1676])).

tff(c_1695,plain,(
    ! [A_506,C_508,D_509] :
      ( m1_subset_1('#skF_2'(A_506,'#skF_5',C_508,D_509),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_506,'#skF_5',C_508,D_509)
      | ~ m1_subset_1(D_509,u1_struct_0(A_506))
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_506),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_508,u1_struct_0(A_506),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_508)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_506)
      | ~ v2_pre_topc(A_506)
      | v2_struct_0(A_506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_58,c_1685])).

tff(c_1916,plain,(
    ! [A_560,C_561,D_562] :
      ( m1_subset_1('#skF_2'(A_560,'#skF_5',C_561,D_562),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_560,'#skF_5',C_561,D_562)
      | ~ m1_subset_1(D_562,u1_struct_0(A_560))
      | ~ m1_subset_1(C_561,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_560),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_561,u1_struct_0(A_560),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_561)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1695])).

tff(c_1921,plain,(
    ! [D_562] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1916])).

tff(c_1927,plain,(
    ! [D_562] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_1921])).

tff(c_1932,plain,(
    ! [D_563] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_563),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_563)
      | ~ m1_subset_1(D_563,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1927])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1963,plain,(
    ! [D_564] :
      ( r1_tarski('#skF_2'('#skF_3','#skF_5','#skF_6',D_564),u1_struct_0('#skF_4'))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_564)
      | ~ m1_subset_1(D_564,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1932,c_12])).

tff(c_56,plain,(
    r1_tarski(u1_pre_topc('#skF_5'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_154,plain,(
    ! [B_212,A_213] :
      ( r2_hidden(B_212,u1_pre_topc(A_213))
      | ~ v3_pre_topc(B_212,A_213)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0(A_213)))
      | ~ l1_pre_topc(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_161,plain,(
    ! [B_212] :
      ( r2_hidden(B_212,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_212,'#skF_5')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_154])).

tff(c_165,plain,(
    ! [B_214] :
      ( r2_hidden(B_214,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_214,'#skF_5')
      | ~ m1_subset_1(B_214,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_161])).

tff(c_171,plain,(
    ! [A_215] :
      ( r2_hidden(A_215,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(A_215,'#skF_5')
      | ~ r1_tarski(A_215,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_165])).

tff(c_114,plain,(
    ! [A_198,C_199,B_200] :
      ( m1_subset_1(A_198,C_199)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(C_199))
      | ~ r2_hidden(A_198,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_122,plain,(
    ! [A_198,B_13,A_12] :
      ( m1_subset_1(A_198,B_13)
      | ~ r2_hidden(A_198,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_114])).

tff(c_1019,plain,(
    ! [A_374,B_375] :
      ( m1_subset_1(A_374,B_375)
      | ~ r1_tarski(u1_pre_topc('#skF_5'),B_375)
      | ~ v3_pre_topc(A_374,'#skF_5')
      | ~ r1_tarski(A_374,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_171,c_122])).

tff(c_1022,plain,(
    ! [A_374] :
      ( m1_subset_1(A_374,u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc(A_374,'#skF_5')
      | ~ r1_tarski(A_374,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_56,c_1019])).

tff(c_2097,plain,(
    ! [D_580] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_580),u1_pre_topc('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_580),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_580)
      | ~ m1_subset_1(D_580,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1963,c_1022])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    ! [C_192,B_193,A_194] :
      ( ~ v1_xboole_0(C_192)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(C_192))
      | ~ r2_hidden(A_194,B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_109,plain,(
    ! [B_195,A_196,A_197] :
      ( ~ v1_xboole_0(B_195)
      | ~ r2_hidden(A_196,A_197)
      | ~ r1_tarski(A_197,B_195) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_130,plain,(
    ! [B_206,B_207,A_208] :
      ( ~ v1_xboole_0(B_206)
      | ~ r1_tarski(B_207,B_206)
      | v1_xboole_0(B_207)
      | ~ m1_subset_1(A_208,B_207) ) ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_139,plain,(
    ! [A_208] :
      ( ~ v1_xboole_0(u1_pre_topc('#skF_4'))
      | v1_xboole_0(u1_pre_topc('#skF_5'))
      | ~ m1_subset_1(A_208,u1_pre_topc('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_56,c_130])).

tff(c_140,plain,(
    ~ v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_968,plain,(
    ! [B_368,A_369] :
      ( v3_pre_topc(B_368,A_369)
      | ~ r2_hidden(B_368,u1_pre_topc(A_369))
      | ~ m1_subset_1(B_368,k1_zfmisc_1(u1_struct_0(A_369)))
      | ~ l1_pre_topc(A_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1003,plain,(
    ! [A_372,A_373] :
      ( v3_pre_topc(A_372,A_373)
      | ~ r2_hidden(A_372,u1_pre_topc(A_373))
      | ~ l1_pre_topc(A_373)
      | ~ r1_tarski(A_372,u1_struct_0(A_373)) ) ),
    inference(resolution,[status(thm)],[c_14,c_968])).

tff(c_1018,plain,(
    ! [A_10,A_373] :
      ( v3_pre_topc(A_10,A_373)
      | ~ l1_pre_topc(A_373)
      | ~ r1_tarski(A_10,u1_struct_0(A_373))
      | v1_xboole_0(u1_pre_topc(A_373))
      | ~ m1_subset_1(A_10,u1_pre_topc(A_373)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1003])).

tff(c_1966,plain,(
    ! [D_564] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_564),'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | v1_xboole_0(u1_pre_topc('#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_564),u1_pre_topc('#skF_4'))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_564)
      | ~ m1_subset_1(D_564,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1963,c_1018])).

tff(c_1976,plain,(
    ! [D_564] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_564),'#skF_4')
      | v1_xboole_0(u1_pre_topc('#skF_4'))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_564),u1_pre_topc('#skF_4'))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_564)
      | ~ m1_subset_1(D_564,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1966])).

tff(c_1977,plain,(
    ! [D_564] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_564),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_564),u1_pre_topc('#skF_4'))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_564)
      | ~ m1_subset_1(D_564,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_1976])).

tff(c_2134,plain,(
    ! [D_586] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_586),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_586),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_586)
      | ~ m1_subset_1(D_586,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2097,c_1977])).

tff(c_2138,plain,(
    ! [D_492] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_492),'#skF_4')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_492)
      | ~ m1_subset_1(D_492,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1644,c_2134])).

tff(c_1928,plain,(
    ! [D_562] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1927])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1816,plain,(
    ! [A_521,B_522,C_523,D_524] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_521),u1_struct_0(B_522),C_523,D_524),'#skF_2'(A_521,B_522,C_523,D_524))
      | r1_tmap_1(A_521,B_522,C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0(B_522))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0(B_522))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc(B_522)
      | ~ v2_pre_topc(B_522)
      | v2_struct_0(B_522)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1830,plain,(
    ! [A_521,C_523,D_524] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_521),u1_struct_0('#skF_4'),C_523,D_524),'#skF_2'(A_521,'#skF_5',C_523,D_524))
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1816])).

tff(c_1841,plain,(
    ! [A_521,C_523,D_524] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_521),u1_struct_0('#skF_4'),C_523,D_524),'#skF_2'(A_521,'#skF_5',C_523,D_524))
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_523)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_58,c_1830])).

tff(c_1842,plain,(
    ! [A_521,C_523,D_524] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_521),u1_struct_0('#skF_4'),C_523,D_524),'#skF_2'(A_521,'#skF_5',C_523,D_524))
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1841])).

tff(c_2102,plain,(
    ! [C_582,E_581,A_585,B_583,D_584] :
      ( v3_pre_topc('#skF_1'(E_581,C_582,B_583,D_584,A_585),A_585)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_585),u1_struct_0(B_583),C_582,D_584),E_581)
      | ~ v3_pre_topc(E_581,B_583)
      | ~ m1_subset_1(E_581,k1_zfmisc_1(u1_struct_0(B_583)))
      | ~ r1_tmap_1(A_585,B_583,C_582,D_584)
      | ~ m1_subset_1(D_584,u1_struct_0(A_585))
      | ~ m1_subset_1(C_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_585),u1_struct_0(B_583))))
      | ~ v1_funct_2(C_582,u1_struct_0(A_585),u1_struct_0(B_583))
      | ~ v1_funct_1(C_582)
      | ~ l1_pre_topc(B_583)
      | ~ v2_pre_topc(B_583)
      | v2_struct_0(B_583)
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2104,plain,(
    ! [A_521,C_523,D_524] :
      ( v3_pre_topc('#skF_1'('#skF_2'(A_521,'#skF_5',C_523,D_524),C_523,'#skF_4',D_524,A_521),A_521)
      | ~ v3_pre_topc('#skF_2'(A_521,'#skF_5',C_523,D_524),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_521,'#skF_5',C_523,D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_521,'#skF_4',C_523,D_524)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(resolution,[status(thm)],[c_1842,c_2102])).

tff(c_2122,plain,(
    ! [A_521,C_523,D_524] :
      ( v3_pre_topc('#skF_1'('#skF_2'(A_521,'#skF_5',C_523,D_524),C_523,'#skF_4',D_524,A_521),A_521)
      | ~ v3_pre_topc('#skF_2'(A_521,'#skF_5',C_523,D_524),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_521,'#skF_5',C_523,D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_521,'#skF_4',C_523,D_524)
      | v2_struct_0('#skF_4')
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2104])).

tff(c_7483,plain,(
    ! [A_1248,C_1249,D_1250] :
      ( v3_pre_topc('#skF_1'('#skF_2'(A_1248,'#skF_5',C_1249,D_1250),C_1249,'#skF_4',D_1250,A_1248),A_1248)
      | ~ v3_pre_topc('#skF_2'(A_1248,'#skF_5',C_1249,D_1250),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_1248,'#skF_5',C_1249,D_1250),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_1248,'#skF_4',C_1249,D_1250)
      | r1_tmap_1(A_1248,'#skF_5',C_1249,D_1250)
      | ~ m1_subset_1(D_1250,u1_struct_0(A_1248))
      | ~ m1_subset_1(C_1249,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1248),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1249,u1_struct_0(A_1248),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1249)
      | ~ l1_pre_topc(A_1248)
      | ~ v2_pre_topc(A_1248)
      | v2_struct_0(A_1248) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2122])).

tff(c_7485,plain,(
    ! [D_562] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1928,c_7483])).

tff(c_7491,plain,(
    ! [D_562] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | v2_struct_0('#skF_3')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_50,c_7485])).

tff(c_7492,plain,(
    ! [D_562] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7491])).

tff(c_2171,plain,(
    ! [A_600,B_598,D_599,E_596,C_597] :
      ( m1_subset_1('#skF_1'(E_596,C_597,B_598,D_599,A_600),k1_zfmisc_1(u1_struct_0(A_600)))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_600),u1_struct_0(B_598),C_597,D_599),E_596)
      | ~ v3_pre_topc(E_596,B_598)
      | ~ m1_subset_1(E_596,k1_zfmisc_1(u1_struct_0(B_598)))
      | ~ r1_tmap_1(A_600,B_598,C_597,D_599)
      | ~ m1_subset_1(D_599,u1_struct_0(A_600))
      | ~ m1_subset_1(C_597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_600),u1_struct_0(B_598))))
      | ~ v1_funct_2(C_597,u1_struct_0(A_600),u1_struct_0(B_598))
      | ~ v1_funct_1(C_597)
      | ~ l1_pre_topc(B_598)
      | ~ v2_pre_topc(B_598)
      | v2_struct_0(B_598)
      | ~ l1_pre_topc(A_600)
      | ~ v2_pre_topc(A_600)
      | v2_struct_0(A_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2175,plain,(
    ! [A_521,C_523,D_524] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_521,'#skF_5',C_523,D_524),C_523,'#skF_4',D_524,A_521),k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ v3_pre_topc('#skF_2'(A_521,'#skF_5',C_523,D_524),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_521,'#skF_5',C_523,D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_521,'#skF_4',C_523,D_524)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(resolution,[status(thm)],[c_1842,c_2171])).

tff(c_2197,plain,(
    ! [A_521,C_523,D_524] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_521,'#skF_5',C_523,D_524),C_523,'#skF_4',D_524,A_521),k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ v3_pre_topc('#skF_2'(A_521,'#skF_5',C_523,D_524),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_521,'#skF_5',C_523,D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_521,'#skF_4',C_523,D_524)
      | v2_struct_0('#skF_4')
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2175])).

tff(c_2198,plain,(
    ! [A_521,C_523,D_524] :
      ( m1_subset_1('#skF_1'('#skF_2'(A_521,'#skF_5',C_523,D_524),C_523,'#skF_4',D_524,A_521),k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ v3_pre_topc('#skF_2'(A_521,'#skF_5',C_523,D_524),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_521,'#skF_5',C_523,D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_521,'#skF_4',C_523,D_524)
      | r1_tmap_1(A_521,'#skF_5',C_523,D_524)
      | ~ m1_subset_1(D_524,u1_struct_0(A_521))
      | ~ m1_subset_1(C_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_521),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_523,u1_struct_0(A_521),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_523)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2197])).

tff(c_2035,plain,(
    ! [A_574,C_575,D_576] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_574),u1_struct_0('#skF_4'),C_575,D_576),'#skF_2'(A_574,'#skF_5',C_575,D_576))
      | r1_tmap_1(A_574,'#skF_5',C_575,D_576)
      | ~ m1_subset_1(D_576,u1_struct_0(A_574))
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_575,u1_struct_0(A_574),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_575)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1841])).

tff(c_26,plain,(
    ! [B_70,E_119,D_112,C_98,A_14] :
      ( r2_hidden(D_112,'#skF_1'(E_119,C_98,B_70,D_112,A_14))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0(B_70),C_98,D_112),E_119)
      | ~ v3_pre_topc(E_119,B_70)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(u1_struct_0(B_70)))
      | ~ r1_tmap_1(A_14,B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2041,plain,(
    ! [D_576,A_574,C_575] :
      ( r2_hidden(D_576,'#skF_1'('#skF_2'(A_574,'#skF_5',C_575,D_576),C_575,'#skF_4',D_576,A_574))
      | ~ v3_pre_topc('#skF_2'(A_574,'#skF_5',C_575,D_576),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_574,'#skF_5',C_575,D_576),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_574,'#skF_4',C_575,D_576)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1(A_574,'#skF_5',C_575,D_576)
      | ~ m1_subset_1(D_576,u1_struct_0(A_574))
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_575,u1_struct_0(A_574),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_575)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(resolution,[status(thm)],[c_2035,c_26])).

tff(c_2055,plain,(
    ! [D_576,A_574,C_575] :
      ( r2_hidden(D_576,'#skF_1'('#skF_2'(A_574,'#skF_5',C_575,D_576),C_575,'#skF_4',D_576,A_574))
      | ~ v3_pre_topc('#skF_2'(A_574,'#skF_5',C_575,D_576),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_574,'#skF_5',C_575,D_576),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_574,'#skF_4',C_575,D_576)
      | v2_struct_0('#skF_4')
      | r1_tmap_1(A_574,'#skF_5',C_575,D_576)
      | ~ m1_subset_1(D_576,u1_struct_0(A_574))
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_574),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_575,u1_struct_0(A_574),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_575)
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2041])).

tff(c_7194,plain,(
    ! [D_1217,A_1218,C_1219] :
      ( r2_hidden(D_1217,'#skF_1'('#skF_2'(A_1218,'#skF_5',C_1219,D_1217),C_1219,'#skF_4',D_1217,A_1218))
      | ~ v3_pre_topc('#skF_2'(A_1218,'#skF_5',C_1219,D_1217),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_1218,'#skF_5',C_1219,D_1217),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_1218,'#skF_4',C_1219,D_1217)
      | r1_tmap_1(A_1218,'#skF_5',C_1219,D_1217)
      | ~ m1_subset_1(D_1217,u1_struct_0(A_1218))
      | ~ m1_subset_1(C_1219,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1218),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1219,u1_struct_0(A_1218),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1219)
      | ~ l1_pre_topc(A_1218)
      | ~ v2_pre_topc(A_1218)
      | v2_struct_0(A_1218) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2055])).

tff(c_7196,plain,(
    ! [D_562] :
      ( r2_hidden(D_562,'#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1928,c_7194])).

tff(c_7202,plain,(
    ! [D_562] :
      ( r2_hidden(D_562,'#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | v2_struct_0('#skF_3')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_50,c_7196])).

tff(c_7203,plain,(
    ! [D_562] :
      ( r2_hidden(D_562,'#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7202])).

tff(c_24,plain,(
    ! [B_70,E_119,D_112,C_98,A_14] :
      ( r1_tarski(k7_relset_1(u1_struct_0(A_14),u1_struct_0(B_70),C_98,'#skF_1'(E_119,C_98,B_70,D_112,A_14)),E_119)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0(B_70),C_98,D_112),E_119)
      | ~ v3_pre_topc(E_119,B_70)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(u1_struct_0(B_70)))
      | ~ r1_tmap_1(A_14,B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1863,plain,(
    ! [B_541,C_540,A_543,F_539,D_542] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_543),u1_struct_0(B_541),C_540,F_539),'#skF_2'(A_543,B_541,C_540,D_542))
      | ~ r2_hidden(D_542,F_539)
      | ~ v3_pre_topc(F_539,A_543)
      | ~ m1_subset_1(F_539,k1_zfmisc_1(u1_struct_0(A_543)))
      | r1_tmap_1(A_543,B_541,C_540,D_542)
      | ~ m1_subset_1(D_542,u1_struct_0(A_543))
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_543),u1_struct_0(B_541))))
      | ~ v1_funct_2(C_540,u1_struct_0(A_543),u1_struct_0(B_541))
      | ~ v1_funct_1(C_540)
      | ~ l1_pre_topc(B_541)
      | ~ v2_pre_topc(B_541)
      | v2_struct_0(B_541)
      | ~ l1_pre_topc(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1869,plain,(
    ! [A_543,C_540,F_539,D_542] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_543),u1_struct_0('#skF_4'),C_540,F_539),'#skF_2'(A_543,'#skF_5',C_540,D_542))
      | ~ r2_hidden(D_542,F_539)
      | ~ v3_pre_topc(F_539,A_543)
      | ~ m1_subset_1(F_539,k1_zfmisc_1(u1_struct_0(A_543)))
      | r1_tmap_1(A_543,'#skF_5',C_540,D_542)
      | ~ m1_subset_1(D_542,u1_struct_0(A_543))
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_543),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(C_540,u1_struct_0(A_543),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_540)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1863])).

tff(c_1874,plain,(
    ! [A_543,C_540,F_539,D_542] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_543),u1_struct_0('#skF_4'),C_540,F_539),'#skF_2'(A_543,'#skF_5',C_540,D_542))
      | ~ r2_hidden(D_542,F_539)
      | ~ v3_pre_topc(F_539,A_543)
      | ~ m1_subset_1(F_539,k1_zfmisc_1(u1_struct_0(A_543)))
      | r1_tmap_1(A_543,'#skF_5',C_540,D_542)
      | ~ m1_subset_1(D_542,u1_struct_0(A_543))
      | ~ m1_subset_1(C_540,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_543),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_540,u1_struct_0(A_543),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_540)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_58,c_1869])).

tff(c_2581,plain,(
    ! [A_663,C_664,F_665,D_666] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_663),u1_struct_0('#skF_4'),C_664,F_665),'#skF_2'(A_663,'#skF_5',C_664,D_666))
      | ~ r2_hidden(D_666,F_665)
      | ~ v3_pre_topc(F_665,A_663)
      | ~ m1_subset_1(F_665,k1_zfmisc_1(u1_struct_0(A_663)))
      | r1_tmap_1(A_663,'#skF_5',C_664,D_666)
      | ~ m1_subset_1(D_666,u1_struct_0(A_663))
      | ~ m1_subset_1(C_664,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_663),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_664,u1_struct_0(A_663),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_664)
      | ~ l1_pre_topc(A_663)
      | ~ v2_pre_topc(A_663)
      | v2_struct_0(A_663) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1874])).

tff(c_2585,plain,(
    ! [D_666,A_14,C_98,D_112] :
      ( ~ r2_hidden(D_666,'#skF_1'('#skF_2'(A_14,'#skF_5',C_98,D_666),C_98,'#skF_4',D_112,A_14))
      | ~ v3_pre_topc('#skF_1'('#skF_2'(A_14,'#skF_5',C_98,D_666),C_98,'#skF_4',D_112,A_14),A_14)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_14,'#skF_5',C_98,D_666),C_98,'#skF_4',D_112,A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | r1_tmap_1(A_14,'#skF_5',C_98,D_666)
      | ~ m1_subset_1(D_666,u1_struct_0(A_14))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0('#skF_4'),C_98,D_112),'#skF_2'(A_14,'#skF_5',C_98,D_666))
      | ~ v3_pre_topc('#skF_2'(A_14,'#skF_5',C_98,D_666),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_14,'#skF_5',C_98,D_666),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_14,'#skF_4',C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_24,c_2581])).

tff(c_2591,plain,(
    ! [D_666,A_14,C_98,D_112] :
      ( ~ r2_hidden(D_666,'#skF_1'('#skF_2'(A_14,'#skF_5',C_98,D_666),C_98,'#skF_4',D_112,A_14))
      | ~ v3_pre_topc('#skF_1'('#skF_2'(A_14,'#skF_5',C_98,D_666),C_98,'#skF_4',D_112,A_14),A_14)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_14,'#skF_5',C_98,D_666),C_98,'#skF_4',D_112,A_14),k1_zfmisc_1(u1_struct_0(A_14)))
      | r1_tmap_1(A_14,'#skF_5',C_98,D_666)
      | ~ m1_subset_1(D_666,u1_struct_0(A_14))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0('#skF_4'),C_98,D_112),'#skF_2'(A_14,'#skF_5',C_98,D_666))
      | ~ v3_pre_topc('#skF_2'(A_14,'#skF_5',C_98,D_666),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_14,'#skF_5',C_98,D_666),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_14,'#skF_4',C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_98)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_2585])).

tff(c_10503,plain,(
    ! [D_1739,A_1740,C_1741,D_1742] :
      ( ~ r2_hidden(D_1739,'#skF_1'('#skF_2'(A_1740,'#skF_5',C_1741,D_1739),C_1741,'#skF_4',D_1742,A_1740))
      | ~ v3_pre_topc('#skF_1'('#skF_2'(A_1740,'#skF_5',C_1741,D_1739),C_1741,'#skF_4',D_1742,A_1740),A_1740)
      | ~ m1_subset_1('#skF_1'('#skF_2'(A_1740,'#skF_5',C_1741,D_1739),C_1741,'#skF_4',D_1742,A_1740),k1_zfmisc_1(u1_struct_0(A_1740)))
      | r1_tmap_1(A_1740,'#skF_5',C_1741,D_1739)
      | ~ m1_subset_1(D_1739,u1_struct_0(A_1740))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_1740),u1_struct_0('#skF_4'),C_1741,D_1742),'#skF_2'(A_1740,'#skF_5',C_1741,D_1739))
      | ~ v3_pre_topc('#skF_2'(A_1740,'#skF_5',C_1741,D_1739),'#skF_4')
      | ~ m1_subset_1('#skF_2'(A_1740,'#skF_5',C_1741,D_1739),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1(A_1740,'#skF_4',C_1741,D_1742)
      | ~ m1_subset_1(D_1742,u1_struct_0(A_1740))
      | ~ m1_subset_1(C_1741,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1740),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1741,u1_struct_0(A_1740),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1741)
      | ~ l1_pre_topc(A_1740)
      | ~ v2_pre_topc(A_1740)
      | v2_struct_0(A_1740) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2591])).

tff(c_10505,plain,(
    ! [D_562] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6',D_562),'#skF_2'('#skF_3','#skF_5','#skF_6',D_562))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7203,c_10503])).

tff(c_10517,plain,(
    ! [D_562] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_6','#skF_4',D_562,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6',D_562),'#skF_2'('#skF_3','#skF_5','#skF_6',D_562))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_562),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_562)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_562)
      | ~ m1_subset_1(D_562,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_50,c_10505])).

tff(c_10528,plain,(
    ! [D_1743] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1743),'#skF_6','#skF_4',D_1743,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1743),'#skF_6','#skF_4',D_1743,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6',D_1743),'#skF_2'('#skF_3','#skF_5','#skF_6',D_1743))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1743),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1743),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_1743)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1743)
      | ~ m1_subset_1(D_1743,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10517])).

tff(c_10532,plain,(
    ! [D_524] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_6','#skF_4',D_524,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_6','#skF_4',D_524,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_524)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_524)
      | ~ m1_subset_1(D_524,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1842,c_10528])).

tff(c_10538,plain,(
    ! [D_524] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_6','#skF_4',D_524,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_6','#skF_4',D_524,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_524)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_524)
      | ~ m1_subset_1(D_524,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_50,c_10532])).

tff(c_10541,plain,(
    ! [D_1744] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1744),'#skF_6','#skF_4',D_1744,'#skF_3'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1744),'#skF_6','#skF_4',D_1744,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1744),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1744),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_1744)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1744)
      | ~ m1_subset_1(D_1744,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10538])).

tff(c_10545,plain,(
    ! [D_524] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_6','#skF_4',D_524,'#skF_3'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_524)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_524)
      | ~ m1_subset_1(D_524,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2198,c_10541])).

tff(c_10555,plain,(
    ! [D_524] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_6','#skF_4',D_524,'#skF_3'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_524)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_524)
      | ~ m1_subset_1(D_524,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_50,c_10545])).

tff(c_10559,plain,(
    ! [D_1745] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1745),'#skF_6','#skF_4',D_1745,'#skF_3'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1745),'#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1745),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_1745)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1745)
      | ~ m1_subset_1(D_1745,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_10555])).

tff(c_10571,plain,(
    ! [D_1746] :
      ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1746),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1746),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_1746)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1746)
      | ~ m1_subset_1(D_1746,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7492,c_10559])).

tff(c_10580,plain,(
    ! [D_1747] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1747),'#skF_4')
      | ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_1747)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1747)
      | ~ m1_subset_1(D_1747,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1928,c_10571])).

tff(c_10585,plain,(
    ! [D_1748] :
      ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_6',D_1748)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1748)
      | ~ m1_subset_1(D_1748,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2138,c_10580])).

tff(c_10596,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_6','#skF_8')
    | r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_10585])).

tff(c_10601,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10596])).

tff(c_10603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1582,c_10601])).

tff(c_10605,plain,(
    v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_10721,plain,(
    ! [B_1774,C_1776,A_1778,D_1777,F_1775] :
      ( r1_funct_2(A_1778,B_1774,C_1776,D_1777,F_1775,F_1775)
      | ~ m1_subset_1(F_1775,k1_zfmisc_1(k2_zfmisc_1(C_1776,D_1777)))
      | ~ v1_funct_2(F_1775,C_1776,D_1777)
      | ~ m1_subset_1(F_1775,k1_zfmisc_1(k2_zfmisc_1(A_1778,B_1774)))
      | ~ v1_funct_2(F_1775,A_1778,B_1774)
      | ~ v1_funct_1(F_1775)
      | v1_xboole_0(D_1777)
      | v1_xboole_0(B_1774) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10723,plain,(
    ! [A_1778,B_1774] :
      ( r1_funct_2(A_1778,B_1774,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_7','#skF_7')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_1778,B_1774)))
      | ~ v1_funct_2('#skF_7',A_1778,B_1774)
      | ~ v1_funct_1('#skF_7')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_1774) ) ),
    inference(resolution,[status(thm)],[c_78,c_10721])).

tff(c_10731,plain,(
    ! [A_1778,B_1774] :
      ( r1_funct_2(A_1778,B_1774,u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_7','#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(A_1778,B_1774)))
      | ~ v1_funct_2('#skF_7',A_1778,B_1774)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | v1_xboole_0(B_1774) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_77,c_10723])).

tff(c_10736,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_10731])).

tff(c_10799,plain,(
    ! [A_1801,B_1802,C_1803,D_1804] :
      ( m1_subset_1('#skF_2'(A_1801,B_1802,C_1803,D_1804),k1_zfmisc_1(u1_struct_0(B_1802)))
      | r1_tmap_1(A_1801,B_1802,C_1803,D_1804)
      | ~ m1_subset_1(D_1804,u1_struct_0(A_1801))
      | ~ m1_subset_1(C_1803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1801),u1_struct_0(B_1802))))
      | ~ v1_funct_2(C_1803,u1_struct_0(A_1801),u1_struct_0(B_1802))
      | ~ v1_funct_1(C_1803)
      | ~ l1_pre_topc(B_1802)
      | ~ v2_pre_topc(B_1802)
      | v2_struct_0(B_1802)
      | ~ l1_pre_topc(A_1801)
      | ~ v2_pre_topc(A_1801)
      | v2_struct_0(A_1801) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_10810,plain,(
    ! [A_1801,C_1803,D_1804] :
      ( m1_subset_1('#skF_2'(A_1801,'#skF_5',C_1803,D_1804),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1(A_1801,'#skF_5',C_1803,D_1804)
      | ~ m1_subset_1(D_1804,u1_struct_0(A_1801))
      | ~ m1_subset_1(C_1803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1801),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1803,u1_struct_0(A_1801),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_1803)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1801)
      | ~ v2_pre_topc(A_1801)
      | v2_struct_0(A_1801) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_10799])).

tff(c_10824,plain,(
    ! [A_1801,C_1803,D_1804] :
      ( m1_subset_1('#skF_2'(A_1801,'#skF_5',C_1803,D_1804),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_1801,'#skF_5',C_1803,D_1804)
      | ~ m1_subset_1(D_1804,u1_struct_0(A_1801))
      | ~ m1_subset_1(C_1803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1801),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1803,u1_struct_0(A_1801),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1803)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1801)
      | ~ v2_pre_topc(A_1801)
      | v2_struct_0(A_1801) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_58,c_10810])).

tff(c_11133,plain,(
    ! [A_1864,C_1865,D_1866] :
      ( m1_subset_1('#skF_2'(A_1864,'#skF_5',C_1865,D_1866),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_1864,'#skF_5',C_1865,D_1866)
      | ~ m1_subset_1(D_1866,u1_struct_0(A_1864))
      | ~ m1_subset_1(C_1865,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1864),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1865,u1_struct_0(A_1864),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1865)
      | ~ l1_pre_topc(A_1864)
      | ~ v2_pre_topc(A_1864)
      | v2_struct_0(A_1864) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_10824])).

tff(c_11135,plain,(
    ! [D_1866] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_7',D_1866),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_1866)
      | ~ m1_subset_1(D_1866,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_11133])).

tff(c_11145,plain,(
    ! [D_1866] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_7',D_1866),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_1866)
      | ~ m1_subset_1(D_1866,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_48,c_77,c_11135])).

tff(c_11155,plain,(
    ! [D_1867] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_7',D_1867),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_1867)
      | ~ m1_subset_1(D_1867,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_11145])).

tff(c_11171,plain,(
    ! [A_126,D_1867] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_126,'#skF_2'('#skF_3','#skF_5','#skF_7',D_1867))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_1867)
      | ~ m1_subset_1(D_1867,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_11155,c_34])).

tff(c_11221,plain,(
    ! [A_1869,D_1870] :
      ( ~ r2_hidden(A_1869,'#skF_2'('#skF_3','#skF_5','#skF_7',D_1870))
      | r1_tmap_1('#skF_3','#skF_5','#skF_7',D_1870)
      | ~ m1_subset_1(D_1870,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10736,c_11171])).

tff(c_11225,plain,(
    ! [D_112] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_7',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_11221])).

tff(c_11232,plain,(
    ! [D_112] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_7',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_60,c_48,c_77,c_58,c_78,c_58,c_11225])).

tff(c_11235,plain,(
    ! [D_1871] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_7',D_1871)
      | ~ m1_subset_1(D_1871,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64,c_11232])).

tff(c_11238,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_11235])).

tff(c_11242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_11238])).

tff(c_11244,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_10731])).

tff(c_11248,plain,(
    ! [B_1876,F_1877,C_1878,D_1879,E_1880,A_1881] :
      ( F_1877 = E_1880
      | ~ r1_funct_2(A_1881,B_1876,C_1878,D_1879,E_1880,F_1877)
      | ~ m1_subset_1(F_1877,k1_zfmisc_1(k2_zfmisc_1(C_1878,D_1879)))
      | ~ v1_funct_2(F_1877,C_1878,D_1879)
      | ~ v1_funct_1(F_1877)
      | ~ m1_subset_1(E_1880,k1_zfmisc_1(k2_zfmisc_1(A_1881,B_1876)))
      | ~ v1_funct_2(E_1880,A_1881,B_1876)
      | ~ v1_funct_1(E_1880)
      | v1_xboole_0(D_1879)
      | v1_xboole_0(B_1876) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_11254,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_79,c_11248])).

tff(c_11267,plain,
    ( '#skF_7' = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_77,c_78,c_11254])).

tff(c_11268,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_11244,c_11267])).

tff(c_11276,plain,(
    ~ r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11268,c_36])).

tff(c_11294,plain,(
    ! [A_1882,B_1883,C_1884,D_1885] :
      ( v3_pre_topc('#skF_2'(A_1882,B_1883,C_1884,D_1885),B_1883)
      | r1_tmap_1(A_1882,B_1883,C_1884,D_1885)
      | ~ m1_subset_1(D_1885,u1_struct_0(A_1882))
      | ~ m1_subset_1(C_1884,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1882),u1_struct_0(B_1883))))
      | ~ v1_funct_2(C_1884,u1_struct_0(A_1882),u1_struct_0(B_1883))
      | ~ v1_funct_1(C_1884)
      | ~ l1_pre_topc(B_1883)
      | ~ v2_pre_topc(B_1883)
      | v2_struct_0(B_1883)
      | ~ l1_pre_topc(A_1882)
      | ~ v2_pre_topc(A_1882)
      | v2_struct_0(A_1882) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_11303,plain,(
    ! [A_1882,C_1884,D_1885] :
      ( v3_pre_topc('#skF_2'(A_1882,'#skF_5',C_1884,D_1885),'#skF_5')
      | r1_tmap_1(A_1882,'#skF_5',C_1884,D_1885)
      | ~ m1_subset_1(D_1885,u1_struct_0(A_1882))
      | ~ m1_subset_1(C_1884,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1882),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1884,u1_struct_0(A_1882),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_1884)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1882)
      | ~ v2_pre_topc(A_1882)
      | v2_struct_0(A_1882) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_11294])).

tff(c_11313,plain,(
    ! [A_1882,C_1884,D_1885] :
      ( v3_pre_topc('#skF_2'(A_1882,'#skF_5',C_1884,D_1885),'#skF_5')
      | r1_tmap_1(A_1882,'#skF_5',C_1884,D_1885)
      | ~ m1_subset_1(D_1885,u1_struct_0(A_1882))
      | ~ m1_subset_1(C_1884,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1882),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1884,u1_struct_0(A_1882),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1884)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1882)
      | ~ v2_pre_topc(A_1882)
      | v2_struct_0(A_1882) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_11303])).

tff(c_11420,plain,(
    ! [A_1908,C_1909,D_1910] :
      ( v3_pre_topc('#skF_2'(A_1908,'#skF_5',C_1909,D_1910),'#skF_5')
      | r1_tmap_1(A_1908,'#skF_5',C_1909,D_1910)
      | ~ m1_subset_1(D_1910,u1_struct_0(A_1908))
      | ~ m1_subset_1(C_1909,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1908),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1909,u1_struct_0(A_1908),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1909)
      | ~ l1_pre_topc(A_1908)
      | ~ v2_pre_topc(A_1908)
      | v2_struct_0(A_1908) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11313])).

tff(c_11425,plain,(
    ! [D_1910] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1910),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1910)
      | ~ m1_subset_1(D_1910,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_11420])).

tff(c_11431,plain,(
    ! [D_1910] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1910),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1910)
      | ~ m1_subset_1(D_1910,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_11425])).

tff(c_11432,plain,(
    ! [D_1910] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1910),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1910)
      | ~ m1_subset_1(D_1910,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_11431])).

tff(c_11350,plain,(
    ! [A_1901,B_1902,C_1903,D_1904] :
      ( m1_subset_1('#skF_2'(A_1901,B_1902,C_1903,D_1904),k1_zfmisc_1(u1_struct_0(B_1902)))
      | r1_tmap_1(A_1901,B_1902,C_1903,D_1904)
      | ~ m1_subset_1(D_1904,u1_struct_0(A_1901))
      | ~ m1_subset_1(C_1903,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1901),u1_struct_0(B_1902))))
      | ~ v1_funct_2(C_1903,u1_struct_0(A_1901),u1_struct_0(B_1902))
      | ~ v1_funct_1(C_1903)
      | ~ l1_pre_topc(B_1902)
      | ~ v2_pre_topc(B_1902)
      | v2_struct_0(B_1902)
      | ~ l1_pre_topc(A_1901)
      | ~ v2_pre_topc(A_1901)
      | v2_struct_0(A_1901) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_11359,plain,(
    ! [A_1901,C_1903,D_1904] :
      ( m1_subset_1('#skF_2'(A_1901,'#skF_5',C_1903,D_1904),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1(A_1901,'#skF_5',C_1903,D_1904)
      | ~ m1_subset_1(D_1904,u1_struct_0(A_1901))
      | ~ m1_subset_1(C_1903,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1901),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1903,u1_struct_0(A_1901),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(C_1903)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1901)
      | ~ v2_pre_topc(A_1901)
      | v2_struct_0(A_1901) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_11350])).

tff(c_11369,plain,(
    ! [A_1901,C_1903,D_1904] :
      ( m1_subset_1('#skF_2'(A_1901,'#skF_5',C_1903,D_1904),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_1901,'#skF_5',C_1903,D_1904)
      | ~ m1_subset_1(D_1904,u1_struct_0(A_1901))
      | ~ m1_subset_1(C_1903,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1901),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1903,u1_struct_0(A_1901),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1903)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_1901)
      | ~ v2_pre_topc(A_1901)
      | v2_struct_0(A_1901) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_58,c_11359])).

tff(c_11550,plain,(
    ! [A_1944,C_1945,D_1946] :
      ( m1_subset_1('#skF_2'(A_1944,'#skF_5',C_1945,D_1946),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1(A_1944,'#skF_5',C_1945,D_1946)
      | ~ m1_subset_1(D_1946,u1_struct_0(A_1944))
      | ~ m1_subset_1(C_1945,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1944),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_1945,u1_struct_0(A_1944),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_1945)
      | ~ l1_pre_topc(A_1944)
      | ~ v2_pre_topc(A_1944)
      | v2_struct_0(A_1944) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_11369])).

tff(c_11555,plain,(
    ! [D_1946] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1946),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1946)
      | ~ m1_subset_1(D_1946,u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_11550])).

tff(c_11561,plain,(
    ! [D_1946] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1946),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1946)
      | ~ m1_subset_1(D_1946,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_54,c_52,c_11555])).

tff(c_11566,plain,(
    ! [D_1947] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1947),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1947)
      | ~ m1_subset_1(D_1947,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_11561])).

tff(c_11597,plain,(
    ! [D_1948] :
      ( r1_tarski('#skF_2'('#skF_3','#skF_5','#skF_6',D_1948),u1_struct_0('#skF_4'))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1948)
      | ~ m1_subset_1(D_1948,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_11566,c_12])).

tff(c_10649,plain,(
    ! [B_1759,A_1760] :
      ( r2_hidden(B_1759,u1_pre_topc(A_1760))
      | ~ v3_pre_topc(B_1759,A_1760)
      | ~ m1_subset_1(B_1759,k1_zfmisc_1(u1_struct_0(A_1760)))
      | ~ l1_pre_topc(A_1760) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10656,plain,(
    ! [B_1759] :
      ( r2_hidden(B_1759,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_1759,'#skF_5')
      | ~ m1_subset_1(B_1759,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_10649])).

tff(c_10660,plain,(
    ! [B_1761] :
      ( r2_hidden(B_1761,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(B_1761,'#skF_5')
      | ~ m1_subset_1(B_1761,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10656])).

tff(c_10666,plain,(
    ! [A_1762] :
      ( r2_hidden(A_1762,u1_pre_topc('#skF_5'))
      | ~ v3_pre_topc(A_1762,'#skF_5')
      | ~ r1_tarski(A_1762,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_10660])).

tff(c_107,plain,(
    ! [B_13,A_194,A_12] :
      ( ~ v1_xboole_0(B_13)
      | ~ r2_hidden(A_194,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_10682,plain,(
    ! [B_13,A_1762] :
      ( ~ v1_xboole_0(B_13)
      | ~ r1_tarski(u1_pre_topc('#skF_5'),B_13)
      | ~ v3_pre_topc(A_1762,'#skF_5')
      | ~ r1_tarski(A_1762,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10666,c_107])).

tff(c_10701,plain,(
    ! [A_1762] :
      ( ~ v3_pre_topc(A_1762,'#skF_5')
      | ~ r1_tarski(A_1762,u1_struct_0('#skF_4')) ) ),
    inference(splitLeft,[status(thm)],[c_10682])).

tff(c_11614,plain,(
    ! [D_1949] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1949),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1949)
      | ~ m1_subset_1(D_1949,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_11597,c_10701])).

tff(c_11619,plain,(
    ! [D_1950] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1950)
      | ~ m1_subset_1(D_1950,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_11432,c_11614])).

tff(c_11622,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_11619])).

tff(c_11626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11276,c_11622])).

tff(c_11628,plain,(
    ! [B_1951] :
      ( ~ v1_xboole_0(B_1951)
      | ~ r1_tarski(u1_pre_topc('#skF_5'),B_1951) ) ),
    inference(splitRight,[status(thm)],[c_10682])).

tff(c_11631,plain,(
    ~ v1_xboole_0(u1_pre_topc('#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_11628])).

tff(c_11635,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10605,c_11631])).

%------------------------------------------------------------------------------
