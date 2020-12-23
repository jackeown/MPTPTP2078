%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:17 EST 2020

% Result     : Theorem 19.10s
% Output     : CNFRefutation 19.10s
% Verified   : 
% Statistics : Number of formulae       :  277 (3852 expanded)
%              Number of leaves         :   49 (1443 expanded)
%              Depth                    :   25
%              Number of atoms          :  851 (34792 expanded)
%              Number of equality atoms :   56 (2045 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_300,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(C),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(D),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                               => ( ( D = A
                                    & r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(D),u1_struct_0(B),E,G) )
                                 => ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,G),F)
                                  <=> r2_funct_2(u1_struct_0(C),u1_struct_0(B),k2_tmap_1(A,B,E,C),F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tmap_1)).

tff(f_77,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_163,axiom,(
    ! [A,B,C,D] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B)
        & v1_funct_1(C)
        & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B))))
        & l1_struct_0(D) )
     => ( v1_funct_1(k2_tmap_1(A,B,C,D))
        & v1_funct_2(k2_tmap_1(A,B,C,D),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k2_tmap_1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_145,axiom,(
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
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_193,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_118,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_231,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,D,C,k2_tmap_1(A,B,E,D)),k2_tmap_1(A,B,E,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_4203,plain,(
    ! [A_758,B_759,D_760] :
      ( r2_funct_2(A_758,B_759,D_760,D_760)
      | ~ m1_subset_1(D_760,k1_zfmisc_1(k2_zfmisc_1(A_758,B_759)))
      | ~ v1_funct_2(D_760,A_758,B_759)
      | ~ v1_funct_1(D_760) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4205,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_4203])).

tff(c_4212,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4205])).

tff(c_54,plain,(
    '#skF_1' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_88,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_103,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_88])).

tff(c_78,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_104,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_78])).

tff(c_116,plain,(
    ! [B_217,A_218] :
      ( l1_pre_topc(B_217)
      | ~ m1_pre_topc(B_217,A_218)
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_116])).

tff(c_128,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_122])).

tff(c_24,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_82,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_58,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_4321,plain,(
    ! [A_771,B_772,C_773,D_774] :
      ( v1_funct_1(k2_tmap_1(A_771,B_772,C_773,D_774))
      | ~ l1_struct_0(D_774)
      | ~ m1_subset_1(C_773,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_771),u1_struct_0(B_772))))
      | ~ v1_funct_2(C_773,u1_struct_0(A_771),u1_struct_0(B_772))
      | ~ v1_funct_1(C_773)
      | ~ l1_struct_0(B_772)
      | ~ l1_struct_0(A_771) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4332,plain,(
    ! [D_774] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_774))
      | ~ l1_struct_0(D_774)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_4321])).

tff(c_4345,plain,(
    ! [D_774] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_774))
      | ~ l1_struct_0(D_774)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_4332])).

tff(c_4364,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4345])).

tff(c_4367,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4364])).

tff(c_4371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_4367])).

tff(c_4372,plain,(
    ! [D_774] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_774))
      | ~ l1_struct_0(D_774) ) ),
    inference(splitRight,[status(thm)],[c_4345])).

tff(c_4387,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_4372])).

tff(c_4390,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_4387])).

tff(c_4394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4390])).

tff(c_4396,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4372])).

tff(c_4328,plain,(
    ! [D_774] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_774))
      | ~ l1_struct_0(D_774)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_4321])).

tff(c_4339,plain,(
    ! [D_774] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_774))
      | ~ l1_struct_0(D_774)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4328])).

tff(c_4459,plain,(
    ! [D_774] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_774))
      | ~ l1_struct_0(D_774)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4396,c_4339])).

tff(c_4460,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4459])).

tff(c_4463,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_4460])).

tff(c_4467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_4463])).

tff(c_4469,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4459])).

tff(c_4373,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4345])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_70,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_107,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_70])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_4488,plain,(
    ! [A_788,B_789,C_790,D_791] :
      ( v1_funct_2(k2_tmap_1(A_788,B_789,C_790,D_791),u1_struct_0(D_791),u1_struct_0(B_789))
      | ~ l1_struct_0(D_791)
      | ~ m1_subset_1(C_790,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_788),u1_struct_0(B_789))))
      | ~ v1_funct_2(C_790,u1_struct_0(A_788),u1_struct_0(B_789))
      | ~ v1_funct_1(C_790)
      | ~ l1_struct_0(B_789)
      | ~ l1_struct_0(A_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4499,plain,(
    ! [D_791] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_791),u1_struct_0(D_791),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_791)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_4488])).

tff(c_4514,plain,(
    ! [D_791] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_791),u1_struct_0(D_791),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_791) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_4396,c_72,c_107,c_4499])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_84,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_90,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_102,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_90])).

tff(c_4163,plain,(
    ! [A_751,B_752,C_753,D_754] :
      ( k2_partfun1(A_751,B_752,C_753,D_754) = k7_relat_1(C_753,D_754)
      | ~ m1_subset_1(C_753,k1_zfmisc_1(k2_zfmisc_1(A_751,B_752)))
      | ~ v1_funct_1(C_753) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4167,plain,(
    ! [D_754] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_754) = k7_relat_1('#skF_5',D_754)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_108,c_4163])).

tff(c_4175,plain,(
    ! [D_754] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_754) = k7_relat_1('#skF_5',D_754) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4167])).

tff(c_5122,plain,(
    ! [A_877,B_878,C_879,D_880] :
      ( k2_partfun1(u1_struct_0(A_877),u1_struct_0(B_878),C_879,u1_struct_0(D_880)) = k2_tmap_1(A_877,B_878,C_879,D_880)
      | ~ m1_pre_topc(D_880,A_877)
      | ~ m1_subset_1(C_879,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_877),u1_struct_0(B_878))))
      | ~ v1_funct_2(C_879,u1_struct_0(A_877),u1_struct_0(B_878))
      | ~ v1_funct_1(C_879)
      | ~ l1_pre_topc(B_878)
      | ~ v2_pre_topc(B_878)
      | v2_struct_0(B_878)
      | ~ l1_pre_topc(A_877)
      | ~ v2_pre_topc(A_877)
      | v2_struct_0(A_877) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5137,plain,(
    ! [D_880] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_880)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_880)
      | ~ m1_pre_topc(D_880,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_5122])).

tff(c_5158,plain,(
    ! [D_880] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_880)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_880)
      | ~ m1_pre_topc(D_880,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_84,c_82,c_72,c_107,c_4175,c_5137])).

tff(c_5160,plain,(
    ! [D_881] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_881)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_881)
      | ~ m1_pre_topc(D_881,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86,c_5158])).

tff(c_227,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( v1_funct_1(k2_partfun1(A_241,B_242,C_243,D_244))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_231,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_244))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_108,c_227])).

tff(c_239,plain,(
    ! [D_244] : v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_244)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_231])).

tff(c_4193,plain,(
    ! [D_244] : v1_funct_1(k7_relat_1('#skF_5',D_244)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4175,c_239])).

tff(c_5197,plain,(
    ! [D_881] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_881))
      | ~ m1_pre_topc(D_881,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5160,c_4193])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_74,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_106,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74])).

tff(c_5262,plain,(
    ! [B_891,D_890,C_887,A_888,E_889] :
      ( v1_funct_2(k3_tmap_1(A_888,B_891,C_887,D_890,E_889),u1_struct_0(D_890),u1_struct_0(B_891))
      | ~ m1_subset_1(E_889,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_887),u1_struct_0(B_891))))
      | ~ v1_funct_2(E_889,u1_struct_0(C_887),u1_struct_0(B_891))
      | ~ v1_funct_1(E_889)
      | ~ m1_pre_topc(D_890,A_888)
      | ~ m1_pre_topc(C_887,A_888)
      | ~ l1_pre_topc(B_891)
      | ~ v2_pre_topc(B_891)
      | v2_struct_0(B_891)
      | ~ l1_pre_topc(A_888)
      | ~ v2_pre_topc(A_888)
      | v2_struct_0(A_888) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_5277,plain,(
    ! [A_888,D_890] :
      ( v1_funct_2(k3_tmap_1(A_888,'#skF_2','#skF_4',D_890,'#skF_5'),u1_struct_0(D_890),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_890,A_888)
      | ~ m1_pre_topc('#skF_4',A_888)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_888)
      | ~ v2_pre_topc(A_888)
      | v2_struct_0(A_888) ) ),
    inference(resolution,[status(thm)],[c_108,c_5262])).

tff(c_5298,plain,(
    ! [A_888,D_890] :
      ( v1_funct_2(k3_tmap_1(A_888,'#skF_2','#skF_4',D_890,'#skF_5'),u1_struct_0(D_890),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_890,A_888)
      | ~ m1_pre_topc('#skF_4',A_888)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_888)
      | ~ v2_pre_topc(A_888)
      | v2_struct_0(A_888) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_107,c_5277])).

tff(c_5299,plain,(
    ! [A_888,D_890] :
      ( v1_funct_2(k3_tmap_1(A_888,'#skF_2','#skF_4',D_890,'#skF_5'),u1_struct_0(D_890),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_890,A_888)
      | ~ m1_pre_topc('#skF_4',A_888)
      | ~ l1_pre_topc(A_888)
      | ~ v2_pre_topc(A_888)
      | v2_struct_0(A_888) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5298])).

tff(c_42,plain,(
    ! [A_53,D_56,E_57,C_55,B_54] :
      ( m1_subset_1(k3_tmap_1(A_53,B_54,C_55,D_56,E_57),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_56),u1_struct_0(B_54))))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55),u1_struct_0(B_54))))
      | ~ v1_funct_2(E_57,u1_struct_0(C_55),u1_struct_0(B_54))
      | ~ v1_funct_1(E_57)
      | ~ m1_pre_topc(D_56,A_53)
      | ~ m1_pre_topc(C_55,A_53)
      | ~ l1_pre_topc(B_54)
      | ~ v2_pre_topc(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_5020,plain,(
    ! [D_862,A_860,B_863,C_859,E_861] :
      ( v1_funct_1(k3_tmap_1(A_860,B_863,C_859,D_862,E_861))
      | ~ m1_subset_1(E_861,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_859),u1_struct_0(B_863))))
      | ~ v1_funct_2(E_861,u1_struct_0(C_859),u1_struct_0(B_863))
      | ~ v1_funct_1(E_861)
      | ~ m1_pre_topc(D_862,A_860)
      | ~ m1_pre_topc(C_859,A_860)
      | ~ l1_pre_topc(B_863)
      | ~ v2_pre_topc(B_863)
      | v2_struct_0(B_863)
      | ~ l1_pre_topc(A_860)
      | ~ v2_pre_topc(A_860)
      | v2_struct_0(A_860) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_5035,plain,(
    ! [A_860,D_862] :
      ( v1_funct_1(k3_tmap_1(A_860,'#skF_2','#skF_4',D_862,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_862,A_860)
      | ~ m1_pre_topc('#skF_4',A_860)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_860)
      | ~ v2_pre_topc(A_860)
      | v2_struct_0(A_860) ) ),
    inference(resolution,[status(thm)],[c_108,c_5020])).

tff(c_5056,plain,(
    ! [A_860,D_862] :
      ( v1_funct_1(k3_tmap_1(A_860,'#skF_2','#skF_4',D_862,'#skF_5'))
      | ~ m1_pre_topc(D_862,A_860)
      | ~ m1_pre_topc('#skF_4',A_860)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_860)
      | ~ v2_pre_topc(A_860)
      | v2_struct_0(A_860) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_107,c_5035])).

tff(c_5057,plain,(
    ! [A_860,D_862] :
      ( v1_funct_1(k3_tmap_1(A_860,'#skF_2','#skF_4',D_862,'#skF_5'))
      | ~ m1_pre_topc(D_862,A_860)
      | ~ m1_pre_topc('#skF_4',A_860)
      | ~ l1_pre_topc(A_860)
      | ~ v2_pre_topc(A_860)
      | v2_struct_0(A_860) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_5056])).

tff(c_4609,plain,(
    ! [F_802,B_805,A_803,D_806,C_804] :
      ( r1_funct_2(A_803,B_805,C_804,D_806,F_802,F_802)
      | ~ m1_subset_1(F_802,k1_zfmisc_1(k2_zfmisc_1(C_804,D_806)))
      | ~ v1_funct_2(F_802,C_804,D_806)
      | ~ m1_subset_1(F_802,k1_zfmisc_1(k2_zfmisc_1(A_803,B_805)))
      | ~ v1_funct_2(F_802,A_803,B_805)
      | ~ v1_funct_1(F_802)
      | v1_xboole_0(D_806)
      | v1_xboole_0(B_805) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4619,plain,(
    ! [A_803,B_805] :
      ( r1_funct_2(A_803,B_805,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_803,B_805)))
      | ~ v1_funct_2('#skF_6',A_803,B_805)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_805) ) ),
    inference(resolution,[status(thm)],[c_62,c_4609])).

tff(c_4636,plain,(
    ! [A_803,B_805] :
      ( r1_funct_2(A_803,B_805,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_803,B_805)))
      | ~ v1_funct_2('#skF_6',A_803,B_805)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_805) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4619])).

tff(c_4770,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4636])).

tff(c_28,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4773,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_4770,c_28])).

tff(c_4776,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4396,c_4773])).

tff(c_4778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4776])).

tff(c_4780,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4636])).

tff(c_52,plain,(
    r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_110,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_4857,plain,(
    ! [A_842,B_844,E_841,D_845,F_840,C_843] :
      ( F_840 = E_841
      | ~ r1_funct_2(A_842,B_844,C_843,D_845,E_841,F_840)
      | ~ m1_subset_1(F_840,k1_zfmisc_1(k2_zfmisc_1(C_843,D_845)))
      | ~ v1_funct_2(F_840,C_843,D_845)
      | ~ v1_funct_1(F_840)
      | ~ m1_subset_1(E_841,k1_zfmisc_1(k2_zfmisc_1(A_842,B_844)))
      | ~ v1_funct_2(E_841,A_842,B_844)
      | ~ v1_funct_1(E_841)
      | v1_xboole_0(D_845)
      | v1_xboole_0(B_844) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4859,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_110,c_4857])).

tff(c_4862,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_107,c_108,c_60,c_58,c_56,c_4859])).

tff(c_4863,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_4780,c_4862])).

tff(c_376,plain,(
    ! [A_267,B_268,C_269,D_270] :
      ( v1_funct_1(k2_tmap_1(A_267,B_268,C_269,D_270))
      | ~ l1_struct_0(D_270)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_267),u1_struct_0(B_268))))
      | ~ v1_funct_2(C_269,u1_struct_0(A_267),u1_struct_0(B_268))
      | ~ v1_funct_1(C_269)
      | ~ l1_struct_0(B_268)
      | ~ l1_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_385,plain,(
    ! [D_270] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_270))
      | ~ l1_struct_0(D_270)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_376])).

tff(c_395,plain,(
    ! [D_270] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_270))
      | ~ l1_struct_0(D_270)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_385])).

tff(c_440,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_443,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_440])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_443])).

tff(c_448,plain,(
    ! [D_270] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_7',D_270))
      | ~ l1_struct_0(D_270) ) ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_473,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_500,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_473])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_500])).

tff(c_506,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_774,plain,(
    ! [C_320,A_319,D_322,B_321,F_318] :
      ( r1_funct_2(A_319,B_321,C_320,D_322,F_318,F_318)
      | ~ m1_subset_1(F_318,k1_zfmisc_1(k2_zfmisc_1(C_320,D_322)))
      | ~ v1_funct_2(F_318,C_320,D_322)
      | ~ m1_subset_1(F_318,k1_zfmisc_1(k2_zfmisc_1(A_319,B_321)))
      | ~ v1_funct_2(F_318,A_319,B_321)
      | ~ v1_funct_1(F_318)
      | v1_xboole_0(D_322)
      | v1_xboole_0(B_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_784,plain,(
    ! [A_319,B_321] :
      ( r1_funct_2(A_319,B_321,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_319,B_321)))
      | ~ v1_funct_2('#skF_6',A_319,B_321)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_321) ) ),
    inference(resolution,[status(thm)],[c_62,c_774])).

tff(c_801,plain,(
    ! [A_319,B_321] :
      ( r1_funct_2(A_319,B_321,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_319,B_321)))
      | ~ v1_funct_2('#skF_6',A_319,B_321)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_784])).

tff(c_839,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_801])).

tff(c_842,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_839,c_28])).

tff(c_845,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_842])).

tff(c_847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_845])).

tff(c_849,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_801])).

tff(c_1090,plain,(
    ! [A_361,F_359,B_363,E_360,C_362,D_364] :
      ( F_359 = E_360
      | ~ r1_funct_2(A_361,B_363,C_362,D_364,E_360,F_359)
      | ~ m1_subset_1(F_359,k1_zfmisc_1(k2_zfmisc_1(C_362,D_364)))
      | ~ v1_funct_2(F_359,C_362,D_364)
      | ~ v1_funct_1(F_359)
      | ~ m1_subset_1(E_360,k1_zfmisc_1(k2_zfmisc_1(A_361,B_363)))
      | ~ v1_funct_2(E_360,A_361,B_363)
      | ~ v1_funct_1(E_360)
      | v1_xboole_0(D_364)
      | v1_xboole_0(B_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1094,plain,
    ( '#skF_7' = '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_110,c_1090])).

tff(c_1102,plain,
    ( '#skF_7' = '#skF_5'
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_107,c_108,c_60,c_58,c_56,c_1094])).

tff(c_1103,plain,(
    '#skF_7' = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_1102])).

tff(c_100,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_105,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_100])).

tff(c_246,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_94,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_300])).

tff(c_109,plain,
    ( ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6')
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_94])).

tff(c_308,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_109])).

tff(c_1117,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_308])).

tff(c_381,plain,(
    ! [D_270] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_270))
      | ~ l1_struct_0(D_270)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_62,c_376])).

tff(c_389,plain,(
    ! [D_270] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_270))
      | ~ l1_struct_0(D_270)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_381])).

tff(c_509,plain,(
    ! [D_270] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_6',D_270))
      | ~ l1_struct_0(D_270)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_389])).

tff(c_510,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_513,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_510])).

tff(c_517,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_513])).

tff(c_519,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_449,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_682,plain,(
    ! [A_297,B_298,C_299,D_300] :
      ( v1_funct_2(k2_tmap_1(A_297,B_298,C_299,D_300),u1_struct_0(D_300),u1_struct_0(B_298))
      | ~ l1_struct_0(D_300)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_297),u1_struct_0(B_298))))
      | ~ v1_funct_2(C_299,u1_struct_0(A_297),u1_struct_0(B_298))
      | ~ v1_funct_1(C_299)
      | ~ l1_struct_0(B_298)
      | ~ l1_struct_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_695,plain,(
    ! [D_300] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_300),u1_struct_0(D_300),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_300)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_682])).

tff(c_713,plain,(
    ! [D_300] :
      ( v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_300),u1_struct_0(D_300),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_506,c_72,c_107,c_695])).

tff(c_36,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( m1_subset_1(k2_tmap_1(A_49,B_50,C_51,D_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_52),u1_struct_0(B_50))))
      | ~ l1_struct_0(D_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49),u1_struct_0(B_50))))
      | ~ v1_funct_2(C_51,u1_struct_0(A_49),u1_struct_0(B_50))
      | ~ v1_funct_1(C_51)
      | ~ l1_struct_0(B_50)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_247,plain,(
    ! [A_248,B_249,C_250,D_251] :
      ( k2_partfun1(A_248,B_249,C_250,D_251) = k7_relat_1(C_250,D_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249)))
      | ~ v1_funct_1(C_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_251,plain,(
    ! [D_251] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_251) = k7_relat_1('#skF_5',D_251)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_108,c_247])).

tff(c_259,plain,(
    ! [D_251] : k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',D_251) = k7_relat_1('#skF_5',D_251) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_251])).

tff(c_1375,plain,(
    ! [A_408,B_409,C_410,D_411] :
      ( k2_partfun1(u1_struct_0(A_408),u1_struct_0(B_409),C_410,u1_struct_0(D_411)) = k2_tmap_1(A_408,B_409,C_410,D_411)
      | ~ m1_pre_topc(D_411,A_408)
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_408),u1_struct_0(B_409))))
      | ~ v1_funct_2(C_410,u1_struct_0(A_408),u1_struct_0(B_409))
      | ~ v1_funct_1(C_410)
      | ~ l1_pre_topc(B_409)
      | ~ v2_pre_topc(B_409)
      | v2_struct_0(B_409)
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1392,plain,(
    ! [D_411] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_411)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_411)
      | ~ m1_pre_topc(D_411,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_108,c_1375])).

tff(c_1417,plain,(
    ! [D_411] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_411)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_411)
      | ~ m1_pre_topc(D_411,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_84,c_82,c_72,c_107,c_259,c_1392])).

tff(c_1419,plain,(
    ! [D_412] :
      ( k7_relat_1('#skF_5',u1_struct_0(D_412)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_412)
      | ~ m1_pre_topc(D_412,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86,c_1417])).

tff(c_277,plain,(
    ! [D_244] : v1_funct_1(k7_relat_1('#skF_5',D_244)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_239])).

tff(c_1461,plain,(
    ! [D_412] :
      ( v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5',D_412))
      | ~ m1_pre_topc(D_412,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1419,c_277])).

tff(c_561,plain,(
    ! [D_284,C_285,A_286,B_287] :
      ( D_284 = C_285
      | ~ r2_funct_2(A_286,B_287,C_285,D_284)
      | ~ m1_subset_1(D_284,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_2(D_284,A_286,B_287)
      | ~ v1_funct_1(D_284)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_2(C_285,A_286,B_287)
      | ~ v1_funct_1(C_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_569,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_246,c_561])).

tff(c_584,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_569])).

tff(c_3704,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_584])).

tff(c_3707,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1461,c_3704])).

tff(c_3714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_3707])).

tff(c_3715,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_584])).

tff(c_3835,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_3715])).

tff(c_3838,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3835])).

tff(c_3842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_506,c_72,c_107,c_108,c_519,c_3838])).

tff(c_3843,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3715])).

tff(c_3963,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3843])).

tff(c_3966,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_713,c_3963])).

tff(c_3970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_3966])).

tff(c_3971,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3843])).

tff(c_130,plain,(
    ! [C_220,A_221,B_222] :
      ( v1_relat_1(C_220)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_108,c_130])).

tff(c_143,plain,(
    ! [C_223,A_224,B_225] :
      ( v4_relat_1(C_223,A_224)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_154,plain,(
    v4_relat_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_108,c_143])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [B_233,A_234] :
      ( k7_relat_1(B_233,A_234) = B_233
      | ~ r1_tarski(k1_relat_1(B_233),A_234)
      | ~ v1_relat_1(B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_180,plain,(
    ! [B_235,A_236] :
      ( k7_relat_1(B_235,A_236) = B_235
      | ~ v4_relat_1(B_235,A_236)
      | ~ v1_relat_1(B_235) ) ),
    inference(resolution,[status(thm)],[c_4,c_175])).

tff(c_183,plain,
    ( k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_154,c_180])).

tff(c_192,plain,(
    k7_relat_1('#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_183])).

tff(c_1464,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1419,c_192])).

tff(c_1473,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1464])).

tff(c_1944,plain,(
    ! [A_470,C_471,B_472,E_474,D_473] :
      ( r2_funct_2(u1_struct_0(C_471),u1_struct_0(B_472),k3_tmap_1(A_470,B_472,D_473,C_471,k2_tmap_1(A_470,B_472,E_474,D_473)),k2_tmap_1(A_470,B_472,E_474,C_471))
      | ~ m1_pre_topc(C_471,D_473)
      | ~ m1_subset_1(E_474,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_470),u1_struct_0(B_472))))
      | ~ v1_funct_2(E_474,u1_struct_0(A_470),u1_struct_0(B_472))
      | ~ v1_funct_1(E_474)
      | ~ m1_pre_topc(D_473,A_470)
      | v2_struct_0(D_473)
      | ~ m1_pre_topc(C_471,A_470)
      | v2_struct_0(C_471)
      | ~ l1_pre_topc(B_472)
      | ~ v2_pre_topc(B_472)
      | v2_struct_0(B_472)
      | ~ l1_pre_topc(A_470)
      | ~ v2_pre_topc(A_470)
      | v2_struct_0(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1949,plain,(
    ! [C_471] :
      ( r2_funct_2(u1_struct_0(C_471),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_471,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_471))
      | ~ m1_pre_topc(C_471,'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_471,'#skF_4')
      | v2_struct_0(C_471)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1473,c_1944])).

tff(c_1955,plain,(
    ! [C_471] :
      ( r2_funct_2(u1_struct_0(C_471),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_471,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_471))
      | ~ m1_pre_topc(C_471,'#skF_4')
      | v2_struct_0(C_471)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_84,c_82,c_106,c_72,c_107,c_108,c_1949])).

tff(c_1956,plain,(
    ! [C_471] :
      ( r2_funct_2(u1_struct_0(C_471),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_471,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_471))
      | ~ m1_pre_topc(C_471,'#skF_4')
      | v2_struct_0(C_471) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86,c_1955])).

tff(c_4051,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3971,c_1956])).

tff(c_4158,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_4051])).

tff(c_4160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1117,c_4158])).

tff(c_4161,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_4397,plain,(
    ! [D_779,C_780,A_781,B_782] :
      ( D_779 = C_780
      | ~ r2_funct_2(A_781,B_782,C_780,D_779)
      | ~ m1_subset_1(D_779,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782)))
      | ~ v1_funct_2(D_779,A_781,B_782)
      | ~ v1_funct_1(D_779)
      | ~ m1_subset_1(C_780,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782)))
      | ~ v1_funct_2(C_780,A_781,B_782)
      | ~ v1_funct_1(C_780) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4405,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4161,c_4397])).

tff(c_4420,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_4405])).

tff(c_7449,plain,
    ( k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4863,c_4863,c_4863,c_4863,c_4420])).

tff(c_7450,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7449])).

tff(c_7453,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5057,c_7450])).

tff(c_7456,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_106,c_104,c_7453])).

tff(c_7458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7456])).

tff(c_7459,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7449])).

tff(c_7603,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_7459])).

tff(c_7606,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_7603])).

tff(c_7609,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_84,c_82,c_106,c_104,c_72,c_107,c_108,c_7606])).

tff(c_7611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86,c_7609])).

tff(c_7612,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7459])).

tff(c_7734,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_7612])).

tff(c_7737,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_5299,c_7734])).

tff(c_7740,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_106,c_104,c_7737])).

tff(c_7742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_7740])).

tff(c_7743,plain,(
    k3_tmap_1('#skF_4','#skF_2','#skF_4','#skF_3','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7612])).

tff(c_5200,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5160,c_192])).

tff(c_5209,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_5200])).

tff(c_5620,plain,(
    ! [E_942,D_941,A_938,B_940,C_939] :
      ( r2_funct_2(u1_struct_0(C_939),u1_struct_0(B_940),k3_tmap_1(A_938,B_940,D_941,C_939,k2_tmap_1(A_938,B_940,E_942,D_941)),k2_tmap_1(A_938,B_940,E_942,C_939))
      | ~ m1_pre_topc(C_939,D_941)
      | ~ m1_subset_1(E_942,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_938),u1_struct_0(B_940))))
      | ~ v1_funct_2(E_942,u1_struct_0(A_938),u1_struct_0(B_940))
      | ~ v1_funct_1(E_942)
      | ~ m1_pre_topc(D_941,A_938)
      | v2_struct_0(D_941)
      | ~ m1_pre_topc(C_939,A_938)
      | v2_struct_0(C_939)
      | ~ l1_pre_topc(B_940)
      | ~ v2_pre_topc(B_940)
      | v2_struct_0(B_940)
      | ~ l1_pre_topc(A_938)
      | ~ v2_pre_topc(A_938)
      | v2_struct_0(A_938) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_5625,plain,(
    ! [C_939] :
      ( r2_funct_2(u1_struct_0(C_939),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_939,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_939))
      | ~ m1_pre_topc(C_939,'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_939,'#skF_4')
      | v2_struct_0(C_939)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5209,c_5620])).

tff(c_5631,plain,(
    ! [C_939] :
      ( r2_funct_2(u1_struct_0(C_939),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_939,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_939))
      | ~ m1_pre_topc(C_939,'#skF_4')
      | v2_struct_0(C_939)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103,c_84,c_82,c_106,c_72,c_107,c_108,c_5625])).

tff(c_5632,plain,(
    ! [C_939] :
      ( r2_funct_2(u1_struct_0(C_939),u1_struct_0('#skF_2'),k3_tmap_1('#skF_4','#skF_2','#skF_4',C_939,'#skF_5'),k2_tmap_1('#skF_4','#skF_2','#skF_5',C_939))
      | ~ m1_pre_topc(C_939,'#skF_4')
      | v2_struct_0(C_939) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_86,c_5631])).

tff(c_7769,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7743,c_5632])).

tff(c_7782,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7769])).

tff(c_7783,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7782])).

tff(c_22,plain,(
    ! [D_22,C_21,A_19,B_20] :
      ( D_22 = C_21
      | ~ r2_funct_2(A_19,B_20,C_21,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(D_22,A_19,B_20)
      | ~ v1_funct_1(D_22)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20)))
      | ~ v1_funct_2(C_21,A_19,B_20)
      | ~ v1_funct_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_7793,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_7783,c_22])).

tff(c_7796,plain,
    ( k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_7793])).

tff(c_28027,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7796])).

tff(c_28079,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_5197,c_28027])).

tff(c_28086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_28079])).

tff(c_28088,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7796])).

tff(c_28087,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7796])).

tff(c_28089,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_28087])).

tff(c_28092,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_28089])).

tff(c_28096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4373,c_4396,c_72,c_107,c_108,c_4469,c_28092])).

tff(c_28098,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_28087])).

tff(c_46,plain,(
    ! [A_53,D_56,E_57,C_55,B_54] :
      ( v1_funct_1(k3_tmap_1(A_53,B_54,C_55,D_56,E_57))
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55),u1_struct_0(B_54))))
      | ~ v1_funct_2(E_57,u1_struct_0(C_55),u1_struct_0(B_54))
      | ~ v1_funct_1(E_57)
      | ~ m1_pre_topc(D_56,A_53)
      | ~ m1_pre_topc(C_55,A_53)
      | ~ l1_pre_topc(B_54)
      | ~ v2_pre_topc(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_28140,plain,(
    ! [A_53,D_56] :
      ( v1_funct_1(k3_tmap_1(A_53,'#skF_2','#skF_3',D_56,k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc(D_56,A_53)
      | ~ m1_pre_topc('#skF_3',A_53)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_28098,c_46])).

tff(c_28236,plain,(
    ! [A_53,D_56] :
      ( v1_funct_1(k3_tmap_1(A_53,'#skF_2','#skF_3',D_56,k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_56,A_53)
      | ~ m1_pre_topc('#skF_3',A_53)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_28088,c_28140])).

tff(c_28237,plain,(
    ! [A_53,D_56] :
      ( v1_funct_1(k3_tmap_1(A_53,'#skF_2','#skF_3',D_56,k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')))
      | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_56,A_53)
      | ~ m1_pre_topc('#skF_3',A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_28236])).

tff(c_28320,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_28237])).

tff(c_28323,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4514,c_28320])).

tff(c_28327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4469,c_28323])).

tff(c_28329,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_28237])).

tff(c_28097,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28087])).

tff(c_32824,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28329,c_28097])).

tff(c_4162,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_32872,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32824,c_4162])).

tff(c_32899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4212,c_32872])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:42:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.10/10.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.10/10.41  
% 19.10/10.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.10/10.42  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 19.10/10.42  
% 19.10/10.42  %Foreground sorts:
% 19.10/10.42  
% 19.10/10.42  
% 19.10/10.42  %Background operators:
% 19.10/10.42  
% 19.10/10.42  
% 19.10/10.42  %Foreground operators:
% 19.10/10.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.10/10.42  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 19.10/10.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.10/10.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.10/10.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.10/10.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.10/10.42  tff('#skF_7', type, '#skF_7': $i).
% 19.10/10.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.10/10.42  tff('#skF_5', type, '#skF_5': $i).
% 19.10/10.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 19.10/10.42  tff('#skF_6', type, '#skF_6': $i).
% 19.10/10.42  tff('#skF_2', type, '#skF_2': $i).
% 19.10/10.42  tff('#skF_3', type, '#skF_3': $i).
% 19.10/10.42  tff('#skF_1', type, '#skF_1': $i).
% 19.10/10.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 19.10/10.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.10/10.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 19.10/10.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.10/10.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.10/10.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 19.10/10.42  tff('#skF_4', type, '#skF_4': $i).
% 19.10/10.42  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 19.10/10.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.10/10.42  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 19.10/10.42  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 19.10/10.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 19.10/10.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.10/10.42  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 19.10/10.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.10/10.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.10/10.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.10/10.42  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 19.10/10.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.10/10.42  
% 19.10/10.45  tff(f_300, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((D = A) & r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(D), u1_struct_0(B), E, G)) => (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, G), F) <=> r2_funct_2(u1_struct_0(C), u1_struct_0(B), k2_tmap_1(A, B, E, C), F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_tmap_1)).
% 19.10/10.45  tff(f_77, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 19.10/10.45  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 19.10/10.45  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 19.10/10.45  tff(f_163, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 19.10/10.45  tff(f_61, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 19.10/10.45  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 19.10/10.45  tff(f_55, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 19.10/10.45  tff(f_193, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 19.10/10.45  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 19.10/10.45  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 19.10/10.45  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 19.10/10.45  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 19.10/10.45  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 19.10/10.45  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 19.10/10.45  tff(f_231, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (m1_pre_topc(C, D) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, D, C, k2_tmap_1(A, B, E, D)), k2_tmap_1(A, B, E, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 19.10/10.45  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_64, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_4203, plain, (![A_758, B_759, D_760]: (r2_funct_2(A_758, B_759, D_760, D_760) | ~m1_subset_1(D_760, k1_zfmisc_1(k2_zfmisc_1(A_758, B_759))) | ~v1_funct_2(D_760, A_758, B_759) | ~v1_funct_1(D_760))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.10/10.45  tff(c_4205, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_4203])).
% 19.10/10.45  tff(c_4212, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4205])).
% 19.10/10.45  tff(c_54, plain, ('#skF_1'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_88, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_103, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_88])).
% 19.10/10.45  tff(c_78, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_104, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_78])).
% 19.10/10.45  tff(c_116, plain, (![B_217, A_218]: (l1_pre_topc(B_217) | ~m1_pre_topc(B_217, A_218) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_88])).
% 19.10/10.45  tff(c_122, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_104, c_116])).
% 19.10/10.45  tff(c_128, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_122])).
% 19.10/10.45  tff(c_24, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.10/10.45  tff(c_82, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_58, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_4321, plain, (![A_771, B_772, C_773, D_774]: (v1_funct_1(k2_tmap_1(A_771, B_772, C_773, D_774)) | ~l1_struct_0(D_774) | ~m1_subset_1(C_773, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_771), u1_struct_0(B_772)))) | ~v1_funct_2(C_773, u1_struct_0(A_771), u1_struct_0(B_772)) | ~v1_funct_1(C_773) | ~l1_struct_0(B_772) | ~l1_struct_0(A_771))), inference(cnfTransformation, [status(thm)], [f_163])).
% 19.10/10.45  tff(c_4332, plain, (![D_774]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_774)) | ~l1_struct_0(D_774) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_4321])).
% 19.10/10.45  tff(c_4345, plain, (![D_774]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_774)) | ~l1_struct_0(D_774) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_4332])).
% 19.10/10.45  tff(c_4364, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4345])).
% 19.10/10.45  tff(c_4367, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4364])).
% 19.10/10.45  tff(c_4371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_4367])).
% 19.10/10.45  tff(c_4372, plain, (![D_774]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_774)) | ~l1_struct_0(D_774))), inference(splitRight, [status(thm)], [c_4345])).
% 19.10/10.45  tff(c_4387, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_4372])).
% 19.10/10.45  tff(c_4390, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_4387])).
% 19.10/10.45  tff(c_4394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_4390])).
% 19.10/10.45  tff(c_4396, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_4372])).
% 19.10/10.45  tff(c_4328, plain, (![D_774]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_774)) | ~l1_struct_0(D_774) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_4321])).
% 19.10/10.45  tff(c_4339, plain, (![D_774]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_774)) | ~l1_struct_0(D_774) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4328])).
% 19.10/10.45  tff(c_4459, plain, (![D_774]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_774)) | ~l1_struct_0(D_774) | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4396, c_4339])).
% 19.10/10.45  tff(c_4460, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_4459])).
% 19.10/10.45  tff(c_4463, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_4460])).
% 19.10/10.45  tff(c_4467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_4463])).
% 19.10/10.45  tff(c_4469, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_4459])).
% 19.10/10.45  tff(c_4373, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_4345])).
% 19.10/10.45  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_70, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_107, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_70])).
% 19.10/10.45  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68])).
% 19.10/10.45  tff(c_4488, plain, (![A_788, B_789, C_790, D_791]: (v1_funct_2(k2_tmap_1(A_788, B_789, C_790, D_791), u1_struct_0(D_791), u1_struct_0(B_789)) | ~l1_struct_0(D_791) | ~m1_subset_1(C_790, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_788), u1_struct_0(B_789)))) | ~v1_funct_2(C_790, u1_struct_0(A_788), u1_struct_0(B_789)) | ~v1_funct_1(C_790) | ~l1_struct_0(B_789) | ~l1_struct_0(A_788))), inference(cnfTransformation, [status(thm)], [f_163])).
% 19.10/10.45  tff(c_4499, plain, (![D_791]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_791), u1_struct_0(D_791), u1_struct_0('#skF_2')) | ~l1_struct_0(D_791) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_4488])).
% 19.10/10.45  tff(c_4514, plain, (![D_791]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_791), u1_struct_0(D_791), u1_struct_0('#skF_2')) | ~l1_struct_0(D_791))), inference(demodulation, [status(thm), theory('equality')], [c_4373, c_4396, c_72, c_107, c_4499])).
% 19.10/10.45  tff(c_86, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_84, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_76, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_90, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_102, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_90])).
% 19.10/10.45  tff(c_4163, plain, (![A_751, B_752, C_753, D_754]: (k2_partfun1(A_751, B_752, C_753, D_754)=k7_relat_1(C_753, D_754) | ~m1_subset_1(C_753, k1_zfmisc_1(k2_zfmisc_1(A_751, B_752))) | ~v1_funct_1(C_753))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.10/10.45  tff(c_4167, plain, (![D_754]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_754)=k7_relat_1('#skF_5', D_754) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_108, c_4163])).
% 19.10/10.45  tff(c_4175, plain, (![D_754]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_754)=k7_relat_1('#skF_5', D_754))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4167])).
% 19.10/10.45  tff(c_5122, plain, (![A_877, B_878, C_879, D_880]: (k2_partfun1(u1_struct_0(A_877), u1_struct_0(B_878), C_879, u1_struct_0(D_880))=k2_tmap_1(A_877, B_878, C_879, D_880) | ~m1_pre_topc(D_880, A_877) | ~m1_subset_1(C_879, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_877), u1_struct_0(B_878)))) | ~v1_funct_2(C_879, u1_struct_0(A_877), u1_struct_0(B_878)) | ~v1_funct_1(C_879) | ~l1_pre_topc(B_878) | ~v2_pre_topc(B_878) | v2_struct_0(B_878) | ~l1_pre_topc(A_877) | ~v2_pre_topc(A_877) | v2_struct_0(A_877))), inference(cnfTransformation, [status(thm)], [f_145])).
% 19.10/10.45  tff(c_5137, plain, (![D_880]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_880))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_880) | ~m1_pre_topc(D_880, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_5122])).
% 19.10/10.45  tff(c_5158, plain, (![D_880]: (k7_relat_1('#skF_5', u1_struct_0(D_880))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_880) | ~m1_pre_topc(D_880, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_84, c_82, c_72, c_107, c_4175, c_5137])).
% 19.10/10.45  tff(c_5160, plain, (![D_881]: (k7_relat_1('#skF_5', u1_struct_0(D_881))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_881) | ~m1_pre_topc(D_881, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_86, c_5158])).
% 19.10/10.45  tff(c_227, plain, (![A_241, B_242, C_243, D_244]: (v1_funct_1(k2_partfun1(A_241, B_242, C_243, D_244)) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))) | ~v1_funct_1(C_243))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.10/10.45  tff(c_231, plain, (![D_244]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_244)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_108, c_227])).
% 19.10/10.45  tff(c_239, plain, (![D_244]: (v1_funct_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_244)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_231])).
% 19.10/10.45  tff(c_4193, plain, (![D_244]: (v1_funct_1(k7_relat_1('#skF_5', D_244)))), inference(demodulation, [status(thm), theory('equality')], [c_4175, c_239])).
% 19.10/10.45  tff(c_5197, plain, (![D_881]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_881)) | ~m1_pre_topc(D_881, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5160, c_4193])).
% 19.10/10.45  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_74, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_106, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74])).
% 19.10/10.45  tff(c_5262, plain, (![B_891, D_890, C_887, A_888, E_889]: (v1_funct_2(k3_tmap_1(A_888, B_891, C_887, D_890, E_889), u1_struct_0(D_890), u1_struct_0(B_891)) | ~m1_subset_1(E_889, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_887), u1_struct_0(B_891)))) | ~v1_funct_2(E_889, u1_struct_0(C_887), u1_struct_0(B_891)) | ~v1_funct_1(E_889) | ~m1_pre_topc(D_890, A_888) | ~m1_pre_topc(C_887, A_888) | ~l1_pre_topc(B_891) | ~v2_pre_topc(B_891) | v2_struct_0(B_891) | ~l1_pre_topc(A_888) | ~v2_pre_topc(A_888) | v2_struct_0(A_888))), inference(cnfTransformation, [status(thm)], [f_193])).
% 19.10/10.45  tff(c_5277, plain, (![A_888, D_890]: (v1_funct_2(k3_tmap_1(A_888, '#skF_2', '#skF_4', D_890, '#skF_5'), u1_struct_0(D_890), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_890, A_888) | ~m1_pre_topc('#skF_4', A_888) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_888) | ~v2_pre_topc(A_888) | v2_struct_0(A_888))), inference(resolution, [status(thm)], [c_108, c_5262])).
% 19.10/10.45  tff(c_5298, plain, (![A_888, D_890]: (v1_funct_2(k3_tmap_1(A_888, '#skF_2', '#skF_4', D_890, '#skF_5'), u1_struct_0(D_890), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_890, A_888) | ~m1_pre_topc('#skF_4', A_888) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_888) | ~v2_pre_topc(A_888) | v2_struct_0(A_888))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_107, c_5277])).
% 19.10/10.45  tff(c_5299, plain, (![A_888, D_890]: (v1_funct_2(k3_tmap_1(A_888, '#skF_2', '#skF_4', D_890, '#skF_5'), u1_struct_0(D_890), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_890, A_888) | ~m1_pre_topc('#skF_4', A_888) | ~l1_pre_topc(A_888) | ~v2_pre_topc(A_888) | v2_struct_0(A_888))), inference(negUnitSimplification, [status(thm)], [c_86, c_5298])).
% 19.10/10.45  tff(c_42, plain, (![A_53, D_56, E_57, C_55, B_54]: (m1_subset_1(k3_tmap_1(A_53, B_54, C_55, D_56, E_57), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_56), u1_struct_0(B_54)))) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55), u1_struct_0(B_54)))) | ~v1_funct_2(E_57, u1_struct_0(C_55), u1_struct_0(B_54)) | ~v1_funct_1(E_57) | ~m1_pre_topc(D_56, A_53) | ~m1_pre_topc(C_55, A_53) | ~l1_pre_topc(B_54) | ~v2_pre_topc(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_193])).
% 19.10/10.45  tff(c_5020, plain, (![D_862, A_860, B_863, C_859, E_861]: (v1_funct_1(k3_tmap_1(A_860, B_863, C_859, D_862, E_861)) | ~m1_subset_1(E_861, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_859), u1_struct_0(B_863)))) | ~v1_funct_2(E_861, u1_struct_0(C_859), u1_struct_0(B_863)) | ~v1_funct_1(E_861) | ~m1_pre_topc(D_862, A_860) | ~m1_pre_topc(C_859, A_860) | ~l1_pre_topc(B_863) | ~v2_pre_topc(B_863) | v2_struct_0(B_863) | ~l1_pre_topc(A_860) | ~v2_pre_topc(A_860) | v2_struct_0(A_860))), inference(cnfTransformation, [status(thm)], [f_193])).
% 19.10/10.45  tff(c_5035, plain, (![A_860, D_862]: (v1_funct_1(k3_tmap_1(A_860, '#skF_2', '#skF_4', D_862, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_862, A_860) | ~m1_pre_topc('#skF_4', A_860) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_860) | ~v2_pre_topc(A_860) | v2_struct_0(A_860))), inference(resolution, [status(thm)], [c_108, c_5020])).
% 19.10/10.45  tff(c_5056, plain, (![A_860, D_862]: (v1_funct_1(k3_tmap_1(A_860, '#skF_2', '#skF_4', D_862, '#skF_5')) | ~m1_pre_topc(D_862, A_860) | ~m1_pre_topc('#skF_4', A_860) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_860) | ~v2_pre_topc(A_860) | v2_struct_0(A_860))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_107, c_5035])).
% 19.10/10.45  tff(c_5057, plain, (![A_860, D_862]: (v1_funct_1(k3_tmap_1(A_860, '#skF_2', '#skF_4', D_862, '#skF_5')) | ~m1_pre_topc(D_862, A_860) | ~m1_pre_topc('#skF_4', A_860) | ~l1_pre_topc(A_860) | ~v2_pre_topc(A_860) | v2_struct_0(A_860))), inference(negUnitSimplification, [status(thm)], [c_86, c_5056])).
% 19.10/10.45  tff(c_4609, plain, (![F_802, B_805, A_803, D_806, C_804]: (r1_funct_2(A_803, B_805, C_804, D_806, F_802, F_802) | ~m1_subset_1(F_802, k1_zfmisc_1(k2_zfmisc_1(C_804, D_806))) | ~v1_funct_2(F_802, C_804, D_806) | ~m1_subset_1(F_802, k1_zfmisc_1(k2_zfmisc_1(A_803, B_805))) | ~v1_funct_2(F_802, A_803, B_805) | ~v1_funct_1(F_802) | v1_xboole_0(D_806) | v1_xboole_0(B_805))), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.10/10.45  tff(c_4619, plain, (![A_803, B_805]: (r1_funct_2(A_803, B_805, u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_803, B_805))) | ~v1_funct_2('#skF_6', A_803, B_805) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_805))), inference(resolution, [status(thm)], [c_62, c_4609])).
% 19.10/10.45  tff(c_4636, plain, (![A_803, B_805]: (r1_funct_2(A_803, B_805, u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_803, B_805))) | ~v1_funct_2('#skF_6', A_803, B_805) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_805))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_4619])).
% 19.10/10.45  tff(c_4770, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_4636])).
% 19.10/10.45  tff(c_28, plain, (![A_27]: (~v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.10/10.45  tff(c_4773, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_4770, c_28])).
% 19.10/10.45  tff(c_4776, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4396, c_4773])).
% 19.10/10.45  tff(c_4778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_4776])).
% 19.10/10.45  tff(c_4780, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_4636])).
% 19.10/10.45  tff(c_52, plain, (r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_110, plain, (r1_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 19.10/10.45  tff(c_4857, plain, (![A_842, B_844, E_841, D_845, F_840, C_843]: (F_840=E_841 | ~r1_funct_2(A_842, B_844, C_843, D_845, E_841, F_840) | ~m1_subset_1(F_840, k1_zfmisc_1(k2_zfmisc_1(C_843, D_845))) | ~v1_funct_2(F_840, C_843, D_845) | ~v1_funct_1(F_840) | ~m1_subset_1(E_841, k1_zfmisc_1(k2_zfmisc_1(A_842, B_844))) | ~v1_funct_2(E_841, A_842, B_844) | ~v1_funct_1(E_841) | v1_xboole_0(D_845) | v1_xboole_0(B_844))), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.10/10.45  tff(c_4859, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_110, c_4857])).
% 19.10/10.45  tff(c_4862, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_107, c_108, c_60, c_58, c_56, c_4859])).
% 19.10/10.45  tff(c_4863, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_4780, c_4862])).
% 19.10/10.45  tff(c_376, plain, (![A_267, B_268, C_269, D_270]: (v1_funct_1(k2_tmap_1(A_267, B_268, C_269, D_270)) | ~l1_struct_0(D_270) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_267), u1_struct_0(B_268)))) | ~v1_funct_2(C_269, u1_struct_0(A_267), u1_struct_0(B_268)) | ~v1_funct_1(C_269) | ~l1_struct_0(B_268) | ~l1_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_163])).
% 19.10/10.45  tff(c_385, plain, (![D_270]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_270)) | ~l1_struct_0(D_270) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_376])).
% 19.10/10.45  tff(c_395, plain, (![D_270]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_270)) | ~l1_struct_0(D_270) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_385])).
% 19.10/10.45  tff(c_440, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_395])).
% 19.10/10.45  tff(c_443, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_440])).
% 19.10/10.45  tff(c_447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_443])).
% 19.10/10.45  tff(c_448, plain, (![D_270]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_7', D_270)) | ~l1_struct_0(D_270))), inference(splitRight, [status(thm)], [c_395])).
% 19.10/10.45  tff(c_473, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_448])).
% 19.10/10.45  tff(c_500, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_473])).
% 19.10/10.45  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_500])).
% 19.10/10.45  tff(c_506, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_448])).
% 19.10/10.45  tff(c_774, plain, (![C_320, A_319, D_322, B_321, F_318]: (r1_funct_2(A_319, B_321, C_320, D_322, F_318, F_318) | ~m1_subset_1(F_318, k1_zfmisc_1(k2_zfmisc_1(C_320, D_322))) | ~v1_funct_2(F_318, C_320, D_322) | ~m1_subset_1(F_318, k1_zfmisc_1(k2_zfmisc_1(A_319, B_321))) | ~v1_funct_2(F_318, A_319, B_321) | ~v1_funct_1(F_318) | v1_xboole_0(D_322) | v1_xboole_0(B_321))), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.10/10.45  tff(c_784, plain, (![A_319, B_321]: (r1_funct_2(A_319, B_321, u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_319, B_321))) | ~v1_funct_2('#skF_6', A_319, B_321) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_321))), inference(resolution, [status(thm)], [c_62, c_774])).
% 19.10/10.45  tff(c_801, plain, (![A_319, B_321]: (r1_funct_2(A_319, B_321, u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_319, B_321))) | ~v1_funct_2('#skF_6', A_319, B_321) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_321))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_784])).
% 19.10/10.45  tff(c_839, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_801])).
% 19.10/10.45  tff(c_842, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_839, c_28])).
% 19.10/10.45  tff(c_845, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_506, c_842])).
% 19.10/10.45  tff(c_847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_845])).
% 19.10/10.45  tff(c_849, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_801])).
% 19.10/10.45  tff(c_1090, plain, (![A_361, F_359, B_363, E_360, C_362, D_364]: (F_359=E_360 | ~r1_funct_2(A_361, B_363, C_362, D_364, E_360, F_359) | ~m1_subset_1(F_359, k1_zfmisc_1(k2_zfmisc_1(C_362, D_364))) | ~v1_funct_2(F_359, C_362, D_364) | ~v1_funct_1(F_359) | ~m1_subset_1(E_360, k1_zfmisc_1(k2_zfmisc_1(A_361, B_363))) | ~v1_funct_2(E_360, A_361, B_363) | ~v1_funct_1(E_360) | v1_xboole_0(D_364) | v1_xboole_0(B_363))), inference(cnfTransformation, [status(thm)], [f_118])).
% 19.10/10.45  tff(c_1094, plain, ('#skF_7'='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_110, c_1090])).
% 19.10/10.45  tff(c_1102, plain, ('#skF_7'='#skF_5' | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_107, c_108, c_60, c_58, c_56, c_1094])).
% 19.10/10.45  tff(c_1103, plain, ('#skF_7'='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_849, c_1102])).
% 19.10/10.45  tff(c_100, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_105, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_100])).
% 19.10/10.45  tff(c_246, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_105])).
% 19.10/10.45  tff(c_94, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_300])).
% 19.10/10.45  tff(c_109, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6') | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_94])).
% 19.10/10.45  tff(c_308, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_109])).
% 19.10/10.45  tff(c_1117, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1103, c_308])).
% 19.10/10.45  tff(c_381, plain, (![D_270]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_270)) | ~l1_struct_0(D_270) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_62, c_376])).
% 19.10/10.45  tff(c_389, plain, (![D_270]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_270)) | ~l1_struct_0(D_270) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_381])).
% 19.10/10.45  tff(c_509, plain, (![D_270]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_6', D_270)) | ~l1_struct_0(D_270) | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_506, c_389])).
% 19.10/10.45  tff(c_510, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_509])).
% 19.10/10.45  tff(c_513, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_510])).
% 19.10/10.45  tff(c_517, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_513])).
% 19.10/10.45  tff(c_519, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_509])).
% 19.10/10.45  tff(c_449, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_395])).
% 19.10/10.45  tff(c_682, plain, (![A_297, B_298, C_299, D_300]: (v1_funct_2(k2_tmap_1(A_297, B_298, C_299, D_300), u1_struct_0(D_300), u1_struct_0(B_298)) | ~l1_struct_0(D_300) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_297), u1_struct_0(B_298)))) | ~v1_funct_2(C_299, u1_struct_0(A_297), u1_struct_0(B_298)) | ~v1_funct_1(C_299) | ~l1_struct_0(B_298) | ~l1_struct_0(A_297))), inference(cnfTransformation, [status(thm)], [f_163])).
% 19.10/10.45  tff(c_695, plain, (![D_300]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_300), u1_struct_0(D_300), u1_struct_0('#skF_2')) | ~l1_struct_0(D_300) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_682])).
% 19.10/10.45  tff(c_713, plain, (![D_300]: (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_300), u1_struct_0(D_300), u1_struct_0('#skF_2')) | ~l1_struct_0(D_300))), inference(demodulation, [status(thm), theory('equality')], [c_449, c_506, c_72, c_107, c_695])).
% 19.10/10.45  tff(c_36, plain, (![A_49, B_50, C_51, D_52]: (m1_subset_1(k2_tmap_1(A_49, B_50, C_51, D_52), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_52), u1_struct_0(B_50)))) | ~l1_struct_0(D_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49), u1_struct_0(B_50)))) | ~v1_funct_2(C_51, u1_struct_0(A_49), u1_struct_0(B_50)) | ~v1_funct_1(C_51) | ~l1_struct_0(B_50) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_163])).
% 19.10/10.45  tff(c_247, plain, (![A_248, B_249, C_250, D_251]: (k2_partfun1(A_248, B_249, C_250, D_251)=k7_relat_1(C_250, D_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))) | ~v1_funct_1(C_250))), inference(cnfTransformation, [status(thm)], [f_61])).
% 19.10/10.45  tff(c_251, plain, (![D_251]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_251)=k7_relat_1('#skF_5', D_251) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_108, c_247])).
% 19.10/10.45  tff(c_259, plain, (![D_251]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', D_251)=k7_relat_1('#skF_5', D_251))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_251])).
% 19.10/10.45  tff(c_1375, plain, (![A_408, B_409, C_410, D_411]: (k2_partfun1(u1_struct_0(A_408), u1_struct_0(B_409), C_410, u1_struct_0(D_411))=k2_tmap_1(A_408, B_409, C_410, D_411) | ~m1_pre_topc(D_411, A_408) | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_408), u1_struct_0(B_409)))) | ~v1_funct_2(C_410, u1_struct_0(A_408), u1_struct_0(B_409)) | ~v1_funct_1(C_410) | ~l1_pre_topc(B_409) | ~v2_pre_topc(B_409) | v2_struct_0(B_409) | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(cnfTransformation, [status(thm)], [f_145])).
% 19.10/10.45  tff(c_1392, plain, (![D_411]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_411))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_411) | ~m1_pre_topc(D_411, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_1375])).
% 19.10/10.45  tff(c_1417, plain, (![D_411]: (k7_relat_1('#skF_5', u1_struct_0(D_411))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_411) | ~m1_pre_topc(D_411, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_84, c_82, c_72, c_107, c_259, c_1392])).
% 19.10/10.45  tff(c_1419, plain, (![D_412]: (k7_relat_1('#skF_5', u1_struct_0(D_412))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_412) | ~m1_pre_topc(D_412, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_86, c_1417])).
% 19.10/10.45  tff(c_277, plain, (![D_244]: (v1_funct_1(k7_relat_1('#skF_5', D_244)))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_239])).
% 19.10/10.45  tff(c_1461, plain, (![D_412]: (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_412)) | ~m1_pre_topc(D_412, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1419, c_277])).
% 19.10/10.45  tff(c_561, plain, (![D_284, C_285, A_286, B_287]: (D_284=C_285 | ~r2_funct_2(A_286, B_287, C_285, D_284) | ~m1_subset_1(D_284, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_2(D_284, A_286, B_287) | ~v1_funct_1(D_284) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_2(C_285, A_286, B_287) | ~v1_funct_1(C_285))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.10/10.45  tff(c_569, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_246, c_561])).
% 19.10/10.45  tff(c_584, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_569])).
% 19.10/10.45  tff(c_3704, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_584])).
% 19.10/10.45  tff(c_3707, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1461, c_3704])).
% 19.10/10.45  tff(c_3714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_3707])).
% 19.10/10.45  tff(c_3715, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_584])).
% 19.10/10.45  tff(c_3835, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_3715])).
% 19.10/10.45  tff(c_3838, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3835])).
% 19.10/10.45  tff(c_3842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_449, c_506, c_72, c_107, c_108, c_519, c_3838])).
% 19.10/10.45  tff(c_3843, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_3715])).
% 19.10/10.45  tff(c_3963, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_3843])).
% 19.10/10.45  tff(c_3966, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_713, c_3963])).
% 19.10/10.45  tff(c_3970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_519, c_3966])).
% 19.10/10.45  tff(c_3971, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_3843])).
% 19.10/10.45  tff(c_130, plain, (![C_220, A_221, B_222]: (v1_relat_1(C_220) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.10/10.45  tff(c_141, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_108, c_130])).
% 19.10/10.45  tff(c_143, plain, (![C_223, A_224, B_225]: (v4_relat_1(C_223, A_224) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.10/10.45  tff(c_154, plain, (v4_relat_1('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_108, c_143])).
% 19.10/10.45  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.10/10.45  tff(c_175, plain, (![B_233, A_234]: (k7_relat_1(B_233, A_234)=B_233 | ~r1_tarski(k1_relat_1(B_233), A_234) | ~v1_relat_1(B_233))), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.10/10.45  tff(c_180, plain, (![B_235, A_236]: (k7_relat_1(B_235, A_236)=B_235 | ~v4_relat_1(B_235, A_236) | ~v1_relat_1(B_235))), inference(resolution, [status(thm)], [c_4, c_175])).
% 19.10/10.45  tff(c_183, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_154, c_180])).
% 19.10/10.45  tff(c_192, plain, (k7_relat_1('#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_183])).
% 19.10/10.45  tff(c_1464, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1419, c_192])).
% 19.10/10.45  tff(c_1473, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1464])).
% 19.10/10.45  tff(c_1944, plain, (![A_470, C_471, B_472, E_474, D_473]: (r2_funct_2(u1_struct_0(C_471), u1_struct_0(B_472), k3_tmap_1(A_470, B_472, D_473, C_471, k2_tmap_1(A_470, B_472, E_474, D_473)), k2_tmap_1(A_470, B_472, E_474, C_471)) | ~m1_pre_topc(C_471, D_473) | ~m1_subset_1(E_474, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_470), u1_struct_0(B_472)))) | ~v1_funct_2(E_474, u1_struct_0(A_470), u1_struct_0(B_472)) | ~v1_funct_1(E_474) | ~m1_pre_topc(D_473, A_470) | v2_struct_0(D_473) | ~m1_pre_topc(C_471, A_470) | v2_struct_0(C_471) | ~l1_pre_topc(B_472) | ~v2_pre_topc(B_472) | v2_struct_0(B_472) | ~l1_pre_topc(A_470) | ~v2_pre_topc(A_470) | v2_struct_0(A_470))), inference(cnfTransformation, [status(thm)], [f_231])).
% 19.10/10.45  tff(c_1949, plain, (![C_471]: (r2_funct_2(u1_struct_0(C_471), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_471, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_471)) | ~m1_pre_topc(C_471, '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_471, '#skF_4') | v2_struct_0(C_471) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1473, c_1944])).
% 19.10/10.45  tff(c_1955, plain, (![C_471]: (r2_funct_2(u1_struct_0(C_471), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_471, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_471)) | ~m1_pre_topc(C_471, '#skF_4') | v2_struct_0(C_471) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_84, c_82, c_106, c_72, c_107, c_108, c_1949])).
% 19.10/10.45  tff(c_1956, plain, (![C_471]: (r2_funct_2(u1_struct_0(C_471), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_471, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_471)) | ~m1_pre_topc(C_471, '#skF_4') | v2_struct_0(C_471))), inference(negUnitSimplification, [status(thm)], [c_76, c_86, c_1955])).
% 19.10/10.45  tff(c_4051, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3971, c_1956])).
% 19.10/10.45  tff(c_4158, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_4051])).
% 19.10/10.45  tff(c_4160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1117, c_4158])).
% 19.10/10.45  tff(c_4161, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_105])).
% 19.10/10.45  tff(c_4397, plain, (![D_779, C_780, A_781, B_782]: (D_779=C_780 | ~r2_funct_2(A_781, B_782, C_780, D_779) | ~m1_subset_1(D_779, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))) | ~v1_funct_2(D_779, A_781, B_782) | ~v1_funct_1(D_779) | ~m1_subset_1(C_780, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))) | ~v1_funct_2(C_780, A_781, B_782) | ~v1_funct_1(C_780))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.10/10.45  tff(c_4405, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_4161, c_4397])).
% 19.10/10.45  tff(c_4420, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_4405])).
% 19.10/10.45  tff(c_7449, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4863, c_4863, c_4863, c_4863, c_4420])).
% 19.10/10.45  tff(c_7450, plain, (~v1_funct_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_7449])).
% 19.10/10.45  tff(c_7453, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5057, c_7450])).
% 19.10/10.45  tff(c_7456, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_106, c_104, c_7453])).
% 19.10/10.45  tff(c_7458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_7456])).
% 19.10/10.45  tff(c_7459, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_7449])).
% 19.10/10.45  tff(c_7603, plain, (~m1_subset_1(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_7459])).
% 19.10/10.45  tff(c_7606, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_7603])).
% 19.10/10.45  tff(c_7609, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_84, c_82, c_106, c_104, c_72, c_107, c_108, c_7606])).
% 19.10/10.45  tff(c_7611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_86, c_7609])).
% 19.10/10.45  tff(c_7612, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_7459])).
% 19.10/10.45  tff(c_7734, plain, (~v1_funct_2(k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_7612])).
% 19.10/10.45  tff(c_7737, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_5299, c_7734])).
% 19.10/10.45  tff(c_7740, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_106, c_104, c_7737])).
% 19.10/10.45  tff(c_7742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_7740])).
% 19.10/10.45  tff(c_7743, plain, (k3_tmap_1('#skF_4', '#skF_2', '#skF_4', '#skF_3', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_7612])).
% 19.10/10.45  tff(c_5200, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5160, c_192])).
% 19.10/10.45  tff(c_5209, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_106, c_5200])).
% 19.10/10.45  tff(c_5620, plain, (![E_942, D_941, A_938, B_940, C_939]: (r2_funct_2(u1_struct_0(C_939), u1_struct_0(B_940), k3_tmap_1(A_938, B_940, D_941, C_939, k2_tmap_1(A_938, B_940, E_942, D_941)), k2_tmap_1(A_938, B_940, E_942, C_939)) | ~m1_pre_topc(C_939, D_941) | ~m1_subset_1(E_942, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_938), u1_struct_0(B_940)))) | ~v1_funct_2(E_942, u1_struct_0(A_938), u1_struct_0(B_940)) | ~v1_funct_1(E_942) | ~m1_pre_topc(D_941, A_938) | v2_struct_0(D_941) | ~m1_pre_topc(C_939, A_938) | v2_struct_0(C_939) | ~l1_pre_topc(B_940) | ~v2_pre_topc(B_940) | v2_struct_0(B_940) | ~l1_pre_topc(A_938) | ~v2_pre_topc(A_938) | v2_struct_0(A_938))), inference(cnfTransformation, [status(thm)], [f_231])).
% 19.10/10.45  tff(c_5625, plain, (![C_939]: (r2_funct_2(u1_struct_0(C_939), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_939, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_939)) | ~m1_pre_topc(C_939, '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_939, '#skF_4') | v2_struct_0(C_939) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5209, c_5620])).
% 19.10/10.45  tff(c_5631, plain, (![C_939]: (r2_funct_2(u1_struct_0(C_939), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_939, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_939)) | ~m1_pre_topc(C_939, '#skF_4') | v2_struct_0(C_939) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_103, c_84, c_82, c_106, c_72, c_107, c_108, c_5625])).
% 19.10/10.45  tff(c_5632, plain, (![C_939]: (r2_funct_2(u1_struct_0(C_939), u1_struct_0('#skF_2'), k3_tmap_1('#skF_4', '#skF_2', '#skF_4', C_939, '#skF_5'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', C_939)) | ~m1_pre_topc(C_939, '#skF_4') | v2_struct_0(C_939))), inference(negUnitSimplification, [status(thm)], [c_76, c_86, c_5631])).
% 19.10/10.45  tff(c_7769, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7743, c_5632])).
% 19.10/10.45  tff(c_7782, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7769])).
% 19.10/10.45  tff(c_7783, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_80, c_7782])).
% 19.10/10.45  tff(c_22, plain, (![D_22, C_21, A_19, B_20]: (D_22=C_21 | ~r2_funct_2(A_19, B_20, C_21, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(D_22, A_19, B_20) | ~v1_funct_1(D_22) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))) | ~v1_funct_2(C_21, A_19, B_20) | ~v1_funct_1(C_21))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.10/10.45  tff(c_7793, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_7783, c_22])).
% 19.10/10.45  tff(c_7796, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_7793])).
% 19.10/10.45  tff(c_28027, plain, (~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7796])).
% 19.10/10.45  tff(c_28079, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_5197, c_28027])).
% 19.10/10.45  tff(c_28086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_28079])).
% 19.10/10.45  tff(c_28088, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_7796])).
% 19.10/10.45  tff(c_28087, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_7796])).
% 19.10/10.45  tff(c_28089, plain, (~m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_28087])).
% 19.10/10.45  tff(c_28092, plain, (~l1_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_28089])).
% 19.10/10.45  tff(c_28096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4373, c_4396, c_72, c_107, c_108, c_4469, c_28092])).
% 19.10/10.45  tff(c_28098, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_28087])).
% 19.10/10.45  tff(c_46, plain, (![A_53, D_56, E_57, C_55, B_54]: (v1_funct_1(k3_tmap_1(A_53, B_54, C_55, D_56, E_57)) | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_55), u1_struct_0(B_54)))) | ~v1_funct_2(E_57, u1_struct_0(C_55), u1_struct_0(B_54)) | ~v1_funct_1(E_57) | ~m1_pre_topc(D_56, A_53) | ~m1_pre_topc(C_55, A_53) | ~l1_pre_topc(B_54) | ~v2_pre_topc(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_193])).
% 19.10/10.45  tff(c_28140, plain, (![A_53, D_56]: (v1_funct_1(k3_tmap_1(A_53, '#skF_2', '#skF_3', D_56, k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc(D_56, A_53) | ~m1_pre_topc('#skF_3', A_53) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(resolution, [status(thm)], [c_28098, c_46])).
% 19.10/10.45  tff(c_28236, plain, (![A_53, D_56]: (v1_funct_1(k3_tmap_1(A_53, '#skF_2', '#skF_3', D_56, k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_56, A_53) | ~m1_pre_topc('#skF_3', A_53) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_28088, c_28140])).
% 19.10/10.45  tff(c_28237, plain, (![A_53, D_56]: (v1_funct_1(k3_tmap_1(A_53, '#skF_2', '#skF_3', D_56, k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_56, A_53) | ~m1_pre_topc('#skF_3', A_53) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(negUnitSimplification, [status(thm)], [c_86, c_28236])).
% 19.10/10.45  tff(c_28320, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_28237])).
% 19.10/10.45  tff(c_28323, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_4514, c_28320])).
% 19.10/10.45  tff(c_28327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4469, c_28323])).
% 19.10/10.45  tff(c_28329, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_28237])).
% 19.10/10.45  tff(c_28097, plain, (~v1_funct_2(k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_28087])).
% 19.10/10.45  tff(c_32824, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28329, c_28097])).
% 19.10/10.45  tff(c_4162, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_105])).
% 19.10/10.45  tff(c_32872, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32824, c_4162])).
% 19.10/10.45  tff(c_32899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4212, c_32872])).
% 19.10/10.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.10/10.45  
% 19.10/10.45  Inference rules
% 19.10/10.45  ----------------------
% 19.10/10.45  #Ref     : 0
% 19.10/10.45  #Sup     : 7975
% 19.10/10.45  #Fact    : 0
% 19.10/10.45  #Define  : 0
% 19.10/10.45  #Split   : 22
% 19.10/10.45  #Chain   : 0
% 19.10/10.45  #Close   : 0
% 19.10/10.45  
% 19.10/10.45  Ordering : KBO
% 19.10/10.45  
% 19.10/10.45  Simplification rules
% 19.10/10.45  ----------------------
% 19.10/10.45  #Subsume      : 1569
% 19.10/10.45  #Demod        : 14890
% 19.10/10.45  #Tautology    : 3117
% 19.10/10.45  #SimpNegUnit  : 784
% 19.10/10.45  #BackRed      : 179
% 19.10/10.45  
% 19.10/10.45  #Partial instantiations: 0
% 19.10/10.45  #Strategies tried      : 1
% 19.10/10.45  
% 19.10/10.45  Timing (in seconds)
% 19.10/10.45  ----------------------
% 19.10/10.46  Preprocessing        : 0.41
% 19.10/10.46  Parsing              : 0.21
% 19.10/10.46  CNF conversion       : 0.05
% 19.10/10.46  Main loop            : 9.24
% 19.10/10.46  Inferencing          : 2.19
% 19.10/10.46  Reduction            : 4.63
% 19.10/10.46  Demodulation         : 4.03
% 19.10/10.46  BG Simplification    : 0.16
% 19.10/10.46  Subsumption          : 1.92
% 19.10/10.46  Abstraction          : 0.27
% 19.10/10.46  MUC search           : 0.00
% 19.10/10.46  Cooper               : 0.00
% 19.10/10.46  Total                : 9.73
% 19.10/10.46  Index Insertion      : 0.00
% 19.10/10.46  Index Deletion       : 0.00
% 19.10/10.46  Index Matching       : 0.00
% 19.10/10.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
