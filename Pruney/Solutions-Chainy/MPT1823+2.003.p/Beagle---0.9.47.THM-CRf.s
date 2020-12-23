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
% DateTime   : Thu Dec  3 10:28:09 EST 2020

% Result     : Theorem 13.34s
% Output     : CNFRefutation 13.52s
% Verified   : 
% Statistics : Number of formulae       :  173 (9125 expanded)
%              Number of leaves         :   39 (3741 expanded)
%              Depth                    :   28
%              Number of atoms          :  921 (70205 expanded)
%              Number of equality atoms :   33 (4724 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k10_tmap_1,type,(
    k10_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_301,negated_conjecture,(
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
                   => ( A = k1_tsep_1(A,C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                         => r1_funct_2(u1_struct_0(A),u1_struct_0(B),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B),E,k10_tmap_1(A,B,C,D,k2_tmap_1(A,B,E,C),k2_tmap_1(A,B,E,D))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => r1_funct_2(A,B,C,D,E,E) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_196,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_100,axiom,(
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

tff(f_226,axiom,(
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

tff(f_174,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_262,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B),E,k10_tmap_1(A,B,C,D,k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_tmap_1)).

tff(f_41,axiom,(
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

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_106,plain,(
    ! [D_148,B_149,E_153,F_152,C_150,A_151] :
      ( r1_funct_2(A_151,B_149,C_150,D_148,E_153,E_153)
      | ~ m1_subset_1(F_152,k1_zfmisc_1(k2_zfmisc_1(C_150,D_148)))
      | ~ v1_funct_2(F_152,C_150,D_148)
      | ~ v1_funct_1(F_152)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2(E_153,A_151,B_149)
      | ~ v1_funct_1(E_153)
      | v1_xboole_0(D_148)
      | v1_xboole_0(B_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_108,plain,(
    ! [A_151,B_149,E_153] :
      ( r1_funct_2(A_151,B_149,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_153,E_153)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2(E_153,A_151,B_149)
      | ~ v1_funct_1(E_153)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_149) ) ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_111,plain,(
    ! [A_151,B_149,E_153] :
      ( r1_funct_2(A_151,B_149,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_153,E_153)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2(E_153,A_151,B_149)
      | ~ v1_funct_1(E_153)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_108])).

tff(c_112,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_111])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_8])).

tff(c_118,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_115])).

tff(c_121,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_121])).

tff(c_127,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_126,plain,(
    ! [A_151,B_149,E_153] :
      ( r1_funct_2(A_151,B_149,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_153,E_153)
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_149)))
      | ~ v1_funct_2(E_153,A_151,B_149)
      | ~ v1_funct_1(E_153)
      | v1_xboole_0(B_149) ) ),
    inference(splitRight,[status(thm)],[c_111])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_44,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_92,plain,(
    ! [A_141,B_142,C_143] :
      ( m1_pre_topc(k1_tsep_1(A_141,B_142,C_143),A_141)
      | ~ m1_pre_topc(C_143,A_141)
      | v2_struct_0(C_143)
      | ~ m1_pre_topc(B_142,A_141)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_95,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_92])).

tff(c_97,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_46,c_95])).

tff(c_98,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_97])).

tff(c_177,plain,(
    ! [E_181,A_182,C_183,D_185,B_184] :
      ( k3_tmap_1(A_182,B_184,C_183,D_185,E_181) = k2_partfun1(u1_struct_0(C_183),u1_struct_0(B_184),E_181,u1_struct_0(D_185))
      | ~ m1_pre_topc(D_185,C_183)
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183),u1_struct_0(B_184))))
      | ~ v1_funct_2(E_181,u1_struct_0(C_183),u1_struct_0(B_184))
      | ~ v1_funct_1(E_181)
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_pre_topc(C_183,A_182)
      | ~ l1_pre_topc(B_184)
      | ~ v2_pre_topc(B_184)
      | v2_struct_0(B_184)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_181,plain,(
    ! [A_182,D_185] :
      ( k3_tmap_1(A_182,'#skF_2','#skF_1',D_185,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_185))
      | ~ m1_pre_topc(D_185,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_pre_topc('#skF_1',A_182)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_38,c_177])).

tff(c_185,plain,(
    ! [A_182,D_185] :
      ( k3_tmap_1(A_182,'#skF_2','#skF_1',D_185,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_185))
      | ~ m1_pre_topc(D_185,'#skF_1')
      | ~ m1_pre_topc(D_185,A_182)
      | ~ m1_pre_topc('#skF_1',A_182)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_181])).

tff(c_187,plain,(
    ! [A_186,D_187] :
      ( k3_tmap_1(A_186,'#skF_2','#skF_1',D_187,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_187))
      | ~ m1_pre_topc(D_187,'#skF_1')
      | ~ m1_pre_topc(D_187,A_186)
      | ~ m1_pre_topc('#skF_1',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_185])).

tff(c_195,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_187])).

tff(c_207,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_98,c_50,c_195])).

tff(c_208,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_207])).

tff(c_137,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k2_partfun1(u1_struct_0(A_164),u1_struct_0(B_165),C_166,u1_struct_0(D_167)) = k2_tmap_1(A_164,B_165,C_166,D_167)
      | ~ m1_pre_topc(D_167,A_164)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_164),u1_struct_0(B_165))))
      | ~ v1_funct_2(C_166,u1_struct_0(A_164),u1_struct_0(B_165))
      | ~ v1_funct_1(C_166)
      | ~ l1_pre_topc(B_165)
      | ~ v2_pre_topc(B_165)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_139,plain,(
    ! [D_167] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_167)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_167)
      | ~ m1_pre_topc(D_167,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_142,plain,(
    ! [D_167] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_167)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_167)
      | ~ m1_pre_topc(D_167,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_42,c_40,c_139])).

tff(c_143,plain,(
    ! [D_167] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_167)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_167)
      | ~ m1_pre_topc(D_167,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_142])).

tff(c_317,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_143])).

tff(c_324,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_317])).

tff(c_129,plain,(
    ! [C_158,B_159,D_157,A_161,E_160] :
      ( v1_funct_1(k3_tmap_1(A_161,B_159,C_158,D_157,E_160))
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_158),u1_struct_0(B_159))))
      | ~ v1_funct_2(E_160,u1_struct_0(C_158),u1_struct_0(B_159))
      | ~ v1_funct_1(E_160)
      | ~ m1_pre_topc(D_157,A_161)
      | ~ m1_pre_topc(C_158,A_161)
      | ~ l1_pre_topc(B_159)
      | ~ v2_pre_topc(B_159)
      | v2_struct_0(B_159)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_131,plain,(
    ! [A_161,D_157] :
      ( v1_funct_1(k3_tmap_1(A_161,'#skF_2','#skF_1',D_157,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_157,A_161)
      | ~ m1_pre_topc('#skF_1',A_161)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_134,plain,(
    ! [A_161,D_157] :
      ( v1_funct_1(k3_tmap_1(A_161,'#skF_2','#skF_1',D_157,'#skF_5'))
      | ~ m1_pre_topc(D_157,A_161)
      | ~ m1_pre_topc('#skF_1',A_161)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_131])).

tff(c_135,plain,(
    ! [A_161,D_157] :
      ( v1_funct_1(k3_tmap_1(A_161,'#skF_2','#skF_1',D_157,'#skF_5'))
      | ~ m1_pre_topc(D_157,A_161)
      | ~ m1_pre_topc('#skF_1',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_134])).

tff(c_352,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_135])).

tff(c_362,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_98,c_50,c_352])).

tff(c_363,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_362])).

tff(c_153,plain,(
    ! [C_170,D_169,B_171,A_173,E_172] :
      ( v1_funct_2(k3_tmap_1(A_173,B_171,C_170,D_169,E_172),u1_struct_0(D_169),u1_struct_0(B_171))
      | ~ m1_subset_1(E_172,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170),u1_struct_0(B_171))))
      | ~ v1_funct_2(E_172,u1_struct_0(C_170),u1_struct_0(B_171))
      | ~ v1_funct_1(E_172)
      | ~ m1_pre_topc(D_169,A_173)
      | ~ m1_pre_topc(C_170,A_173)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_155,plain,(
    ! [A_173,D_169] :
      ( v1_funct_2(k3_tmap_1(A_173,'#skF_2','#skF_1',D_169,'#skF_5'),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_169,A_173)
      | ~ m1_pre_topc('#skF_1',A_173)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_38,c_153])).

tff(c_158,plain,(
    ! [A_173,D_169] :
      ( v1_funct_2(k3_tmap_1(A_173,'#skF_2','#skF_1',D_169,'#skF_5'),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_169,A_173)
      | ~ m1_pre_topc('#skF_1',A_173)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_155])).

tff(c_159,plain,(
    ! [A_173,D_169] :
      ( v1_funct_2(k3_tmap_1(A_173,'#skF_2','#skF_1',D_169,'#skF_5'),u1_struct_0(D_169),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_169,A_173)
      | ~ m1_pre_topc('#skF_1',A_173)
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_158])).

tff(c_349,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_159])).

tff(c_359,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_98,c_50,c_349])).

tff(c_360,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_359])).

tff(c_28,plain,(
    ! [E_72,C_70,B_69,D_71,A_68] :
      ( m1_subset_1(k3_tmap_1(A_68,B_69,C_70,D_71,E_72),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71),u1_struct_0(B_69))))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_70),u1_struct_0(B_69))))
      | ~ v1_funct_2(E_72,u1_struct_0(C_70),u1_struct_0(B_69))
      | ~ v1_funct_1(E_72)
      | ~ m1_pre_topc(D_71,A_68)
      | ~ m1_pre_topc(C_70,A_68)
      | ~ l1_pre_topc(B_69)
      | ~ v2_pre_topc(B_69)
      | v2_struct_0(B_69)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_346,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_28])).

tff(c_356,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_98,c_50,c_42,c_40,c_38,c_346])).

tff(c_357,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_356])).

tff(c_193,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_187])).

tff(c_203,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_98,c_46,c_193])).

tff(c_204,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_203])).

tff(c_331,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_143])).

tff(c_338,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_331])).

tff(c_375,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_135])).

tff(c_385,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_98,c_46,c_375])).

tff(c_386,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_385])).

tff(c_372,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_159])).

tff(c_382,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_98,c_46,c_372])).

tff(c_383,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_382])).

tff(c_369,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_28])).

tff(c_379,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_98,c_46,c_42,c_40,c_38,c_369])).

tff(c_380,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_379])).

tff(c_523,plain,(
    ! [C_200,E_205,F_203,D_204,B_202,A_201] :
      ( m1_subset_1(k10_tmap_1(A_201,B_202,C_200,D_204,E_205,F_203),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_201,C_200,D_204)),u1_struct_0(B_202))))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_204),u1_struct_0(B_202))))
      | ~ v1_funct_2(F_203,u1_struct_0(D_204),u1_struct_0(B_202))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_200),u1_struct_0(B_202))))
      | ~ v1_funct_2(E_205,u1_struct_0(C_200),u1_struct_0(B_202))
      | ~ v1_funct_1(E_205)
      | ~ m1_pre_topc(D_204,A_201)
      | v2_struct_0(D_204)
      | ~ m1_pre_topc(C_200,A_201)
      | v2_struct_0(C_200)
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_540,plain,(
    ! [B_202,E_205,F_203] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_202,'#skF_3','#skF_4',E_205,F_203),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_202))))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_202))))
      | ~ v1_funct_2(F_203,u1_struct_0('#skF_4'),u1_struct_0(B_202))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_202))))
      | ~ v1_funct_2(E_205,u1_struct_0('#skF_3'),u1_struct_0(B_202))
      | ~ v1_funct_1(E_205)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_523])).

tff(c_549,plain,(
    ! [B_202,E_205,F_203] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_202,'#skF_3','#skF_4',E_205,F_203),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_202))))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_202))))
      | ~ v1_funct_2(F_203,u1_struct_0('#skF_4'),u1_struct_0(B_202))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_202))))
      | ~ v1_funct_2(E_205,u1_struct_0('#skF_3'),u1_struct_0(B_202))
      | ~ v1_funct_1(E_205)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | v2_struct_0(B_202)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_46,c_540])).

tff(c_550,plain,(
    ! [B_202,E_205,F_203] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_202,'#skF_3','#skF_4',E_205,F_203),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_202))))
      | ~ m1_subset_1(F_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_202))))
      | ~ v1_funct_2(F_203,u1_struct_0('#skF_4'),u1_struct_0(B_202))
      | ~ v1_funct_1(F_203)
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_202))))
      | ~ v1_funct_2(E_205,u1_struct_0('#skF_3'),u1_struct_0(B_202))
      | ~ v1_funct_1(E_205)
      | ~ l1_pre_topc(B_202)
      | ~ v2_pre_topc(B_202)
      | v2_struct_0(B_202) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_549])).

tff(c_388,plain,(
    ! [A_195,C_194,B_196,E_199,D_198,F_197] :
      ( v1_funct_2(k10_tmap_1(A_195,B_196,C_194,D_198,E_199,F_197),u1_struct_0(k1_tsep_1(A_195,C_194,D_198)),u1_struct_0(B_196))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_198),u1_struct_0(B_196))))
      | ~ v1_funct_2(F_197,u1_struct_0(D_198),u1_struct_0(B_196))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_194),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_199,u1_struct_0(C_194),u1_struct_0(B_196))
      | ~ v1_funct_1(E_199)
      | ~ m1_pre_topc(D_198,A_195)
      | v2_struct_0(D_198)
      | ~ m1_pre_topc(C_194,A_195)
      | v2_struct_0(C_194)
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | v2_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_391,plain,(
    ! [B_196,E_199,F_197] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_196,'#skF_3','#skF_4',E_199,F_197),u1_struct_0('#skF_1'),u1_struct_0(B_196))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_196))))
      | ~ v1_funct_2(F_197,u1_struct_0('#skF_4'),u1_struct_0(B_196))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_199,u1_struct_0('#skF_3'),u1_struct_0(B_196))
      | ~ v1_funct_1(E_199)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_388])).

tff(c_393,plain,(
    ! [B_196,E_199,F_197] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_196,'#skF_3','#skF_4',E_199,F_197),u1_struct_0('#skF_1'),u1_struct_0(B_196))
      | ~ m1_subset_1(F_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_196))))
      | ~ v1_funct_2(F_197,u1_struct_0('#skF_4'),u1_struct_0(B_196))
      | ~ v1_funct_1(F_197)
      | ~ m1_subset_1(E_199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_196))))
      | ~ v1_funct_2(E_199,u1_struct_0('#skF_3'),u1_struct_0(B_196))
      | ~ v1_funct_1(E_199)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_196)
      | ~ v2_pre_topc(B_196)
      | v2_struct_0(B_196)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_46,c_391])).

tff(c_1381,plain,(
    ! [B_260,E_261,F_262] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_260,'#skF_3','#skF_4',E_261,F_262),u1_struct_0('#skF_1'),u1_struct_0(B_260))
      | ~ m1_subset_1(F_262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_260))))
      | ~ v1_funct_2(F_262,u1_struct_0('#skF_4'),u1_struct_0(B_260))
      | ~ v1_funct_1(F_262)
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_260))))
      | ~ v1_funct_2(E_261,u1_struct_0('#skF_3'),u1_struct_0(B_260))
      | ~ v1_funct_1(E_261)
      | ~ l1_pre_topc(B_260)
      | ~ v2_pre_topc(B_260)
      | v2_struct_0(B_260) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_393])).

tff(c_1389,plain,(
    ! [E_261] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_261,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_261,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_261)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_380,c_1381])).

tff(c_1407,plain,(
    ! [E_261] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_261,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_261,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_261)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_386,c_383,c_1389])).

tff(c_1408,plain,(
    ! [E_261] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_261,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_261,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1407])).

tff(c_20,plain,(
    ! [F_64,D_62,A_59,C_61,E_63,B_60] :
      ( v1_funct_1(k10_tmap_1(A_59,B_60,C_61,D_62,E_63,F_64))
      | ~ m1_subset_1(F_64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62),u1_struct_0(B_60))))
      | ~ v1_funct_2(F_64,u1_struct_0(D_62),u1_struct_0(B_60))
      | ~ v1_funct_1(F_64)
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0(B_60))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_61),u1_struct_0(B_60))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc(D_62,A_59)
      | v2_struct_0(D_62)
      | ~ m1_pre_topc(C_61,A_59)
      | v2_struct_0(C_61)
      | ~ l1_pre_topc(B_60)
      | ~ v2_pre_topc(B_60)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_398,plain,(
    ! [A_59,C_61,E_63] :
      ( v1_funct_1(k10_tmap_1(A_59,'#skF_2',C_61,'#skF_4',E_63,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_61),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc('#skF_4',A_59)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_61,A_59)
      | v2_struct_0(C_61)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_380,c_20])).

tff(c_413,plain,(
    ! [A_59,C_61,E_63] :
      ( v1_funct_1(k10_tmap_1(A_59,'#skF_2',C_61,'#skF_4',E_63,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_63,u1_struct_0(C_61),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_63)
      | ~ m1_pre_topc('#skF_4',A_59)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_61,A_59)
      | v2_struct_0(C_61)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_386,c_383,c_398])).

tff(c_1554,plain,(
    ! [A_274,C_275,E_276] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2',C_275,'#skF_4',E_276,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_275),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_276,u1_struct_0(C_275),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_276)
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc(C_275,A_274)
      | v2_struct_0(C_275)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_48,c_413])).

tff(c_1580,plain,(
    ! [A_274] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc('#skF_3',A_274)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_357,c_1554])).

tff(c_1633,plain,(
    ! [A_274] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc('#skF_3',A_274)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_360,c_1580])).

tff(c_1634,plain,(
    ! [A_274] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc('#skF_3',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1633])).

tff(c_1476,plain,(
    ! [B_267,E_268,F_269] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_267,'#skF_3','#skF_4',E_268,F_269),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_267))))
      | ~ m1_subset_1(F_269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_267))))
      | ~ v1_funct_2(F_269,u1_struct_0('#skF_4'),u1_struct_0(B_267))
      | ~ v1_funct_1(F_269)
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_267))))
      | ~ v1_funct_2(E_268,u1_struct_0('#skF_3'),u1_struct_0(B_267))
      | ~ v1_funct_1(E_268)
      | ~ l1_pre_topc(B_267)
      | ~ v2_pre_topc(B_267)
      | v2_struct_0(B_267) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_549])).

tff(c_247,plain,(
    ! [D_192,E_193,C_188,B_190,F_191,A_189] :
      ( v1_funct_1(k10_tmap_1(A_189,B_190,C_188,D_192,E_193,F_191))
      | ~ m1_subset_1(F_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_192),u1_struct_0(B_190))))
      | ~ v1_funct_2(F_191,u1_struct_0(D_192),u1_struct_0(B_190))
      | ~ v1_funct_1(F_191)
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188),u1_struct_0(B_190))))
      | ~ v1_funct_2(E_193,u1_struct_0(C_188),u1_struct_0(B_190))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc(D_192,A_189)
      | v2_struct_0(D_192)
      | ~ m1_pre_topc(C_188,A_189)
      | v2_struct_0(C_188)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_251,plain,(
    ! [A_189,C_188,E_193] :
      ( v1_funct_1(k10_tmap_1(A_189,'#skF_2',C_188,'#skF_1',E_193,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_193,u1_struct_0(C_188),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc('#skF_1',A_189)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_188,A_189)
      | v2_struct_0(C_188)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_38,c_247])).

tff(c_255,plain,(
    ! [A_189,C_188,E_193] :
      ( v1_funct_1(k10_tmap_1(A_189,'#skF_2',C_188,'#skF_1',E_193,'#skF_5'))
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_193,u1_struct_0(C_188),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc('#skF_1',A_189)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_188,A_189)
      | v2_struct_0(C_188)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_251])).

tff(c_256,plain,(
    ! [A_189,C_188,E_193] :
      ( v1_funct_1(k10_tmap_1(A_189,'#skF_2',C_188,'#skF_1',E_193,'#skF_5'))
      | ~ m1_subset_1(E_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_193,u1_struct_0(C_188),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_193)
      | ~ m1_pre_topc('#skF_1',A_189)
      | ~ m1_pre_topc(C_188,A_189)
      | v2_struct_0(C_188)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_64,c_255])).

tff(c_1479,plain,(
    ! [A_189,E_268,F_269] :
      ( v1_funct_1(k10_tmap_1(A_189,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_268,F_269),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_268,F_269),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_268,F_269))
      | ~ m1_pre_topc('#skF_1',A_189)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189)
      | ~ m1_subset_1(F_269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_269,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_269)
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_268,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_268)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1476,c_256])).

tff(c_1496,plain,(
    ! [A_189,E_268,F_269] :
      ( v1_funct_1(k10_tmap_1(A_189,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_268,F_269),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_268,F_269),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_268,F_269))
      | ~ m1_pre_topc('#skF_1',A_189)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189)
      | ~ m1_subset_1(F_269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_269,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_269)
      | ~ m1_subset_1(E_268,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_268,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_268)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1479])).

tff(c_7312,plain,(
    ! [A_811,E_812,F_813] :
      ( v1_funct_1(k10_tmap_1(A_811,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_812,F_813),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_812,F_813),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_812,F_813))
      | ~ m1_pre_topc('#skF_1',A_811)
      | ~ l1_pre_topc(A_811)
      | ~ v2_pre_topc(A_811)
      | v2_struct_0(A_811)
      | ~ m1_subset_1(F_813,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_813,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_813)
      | ~ m1_subset_1(E_812,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_812,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_812) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_64,c_1496])).

tff(c_7314,plain,(
    ! [A_811,E_261] :
      ( v1_funct_1(k10_tmap_1(A_811,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_261,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_261,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_811)
      | ~ l1_pre_topc(A_811)
      | ~ v2_pre_topc(A_811)
      | v2_struct_0(A_811)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_261,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_261) ) ),
    inference(resolution,[status(thm)],[c_1408,c_7312])).

tff(c_7355,plain,(
    ! [A_823,E_824] :
      ( v1_funct_1(k10_tmap_1(A_823,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_824,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_824,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_823)
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823)
      | ~ m1_subset_1(E_824,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_824,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_824) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_383,c_380,c_7314])).

tff(c_7363,plain,(
    ! [A_823] :
      ( v1_funct_1(k10_tmap_1(A_823,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_823)
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_357,c_7355])).

tff(c_7376,plain,(
    ! [A_823] :
      ( v1_funct_1(k10_tmap_1(A_823,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_823)
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_360,c_7363])).

tff(c_7381,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_7376])).

tff(c_7384,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1634,c_7381])).

tff(c_7387,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_46,c_7384])).

tff(c_7389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7387])).

tff(c_7391,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_7376])).

tff(c_573,plain,(
    ! [B_226,E_223,C_224,D_225,A_227] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_227,C_224,D_225)),u1_struct_0(B_226),E_223,k10_tmap_1(A_227,B_226,C_224,D_225,k3_tmap_1(A_227,B_226,k1_tsep_1(A_227,C_224,D_225),C_224,E_223),k3_tmap_1(A_227,B_226,k1_tsep_1(A_227,C_224,D_225),D_225,E_223)))
      | ~ m1_subset_1(E_223,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_227,C_224,D_225)),u1_struct_0(B_226))))
      | ~ v1_funct_2(E_223,u1_struct_0(k1_tsep_1(A_227,C_224,D_225)),u1_struct_0(B_226))
      | ~ v1_funct_1(E_223)
      | ~ m1_pre_topc(D_225,A_227)
      | v2_struct_0(D_225)
      | ~ m1_pre_topc(C_224,A_227)
      | v2_struct_0(C_224)
      | ~ l1_pre_topc(B_226)
      | ~ v2_pre_topc(B_226)
      | v2_struct_0(B_226)
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5773,plain,(
    ! [A_715,D_713,B_712,C_714,E_711] :
      ( k10_tmap_1(A_715,B_712,C_714,D_713,k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),C_714,E_711),k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),D_713,E_711)) = E_711
      | ~ m1_subset_1(k10_tmap_1(A_715,B_712,C_714,D_713,k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),C_714,E_711),k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),D_713,E_711)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_715,C_714,D_713)),u1_struct_0(B_712))))
      | ~ v1_funct_2(k10_tmap_1(A_715,B_712,C_714,D_713,k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),C_714,E_711),k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),D_713,E_711)),u1_struct_0(k1_tsep_1(A_715,C_714,D_713)),u1_struct_0(B_712))
      | ~ v1_funct_1(k10_tmap_1(A_715,B_712,C_714,D_713,k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),C_714,E_711),k3_tmap_1(A_715,B_712,k1_tsep_1(A_715,C_714,D_713),D_713,E_711)))
      | ~ m1_subset_1(E_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_715,C_714,D_713)),u1_struct_0(B_712))))
      | ~ v1_funct_2(E_711,u1_struct_0(k1_tsep_1(A_715,C_714,D_713)),u1_struct_0(B_712))
      | ~ v1_funct_1(E_711)
      | ~ m1_pre_topc(D_713,A_715)
      | v2_struct_0(D_713)
      | ~ m1_pre_topc(C_714,A_715)
      | v2_struct_0(C_714)
      | ~ l1_pre_topc(B_712)
      | ~ v2_pre_topc(B_712)
      | v2_struct_0(B_712)
      | ~ l1_pre_topc(A_715)
      | ~ v2_pre_topc(A_715)
      | v2_struct_0(A_715) ) ),
    inference(resolution,[status(thm)],[c_573,c_4])).

tff(c_5791,plain,(
    ! [B_712,E_711] :
      ( k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_711),k3_tmap_1('#skF_1',B_712,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_711)) = E_711
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_711),k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_4',E_711)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_712))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_711),k3_tmap_1('#skF_1',B_712,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_711)),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_712))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_711),k3_tmap_1('#skF_1',B_712,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_711)))
      | ~ m1_subset_1(E_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_712))))
      | ~ v1_funct_2(E_711,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_712))
      | ~ v1_funct_1(E_711)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_712)
      | ~ v2_pre_topc(B_712)
      | v2_struct_0(B_712)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_5773])).

tff(c_5800,plain,(
    ! [B_712,E_711] :
      ( k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_3',E_711),k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_4',E_711)) = E_711
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_3',E_711),k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_4',E_711)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_712))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_3',E_711),k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_4',E_711)),u1_struct_0('#skF_1'),u1_struct_0(B_712))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_712,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_3',E_711),k3_tmap_1('#skF_1',B_712,'#skF_1','#skF_4',E_711)))
      | ~ m1_subset_1(E_711,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_712))))
      | ~ v1_funct_2(E_711,u1_struct_0('#skF_1'),u1_struct_0(B_712))
      | ~ v1_funct_1(E_711)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_712)
      | ~ v2_pre_topc(B_712)
      | v2_struct_0(B_712)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_50,c_46,c_44,c_44,c_44,c_44,c_44,c_44,c_44,c_44,c_44,c_44,c_44,c_5791])).

tff(c_10593,plain,(
    ! [B_1067,E_1068] :
      ( k10_tmap_1('#skF_1',B_1067,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_3',E_1068),k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_4',E_1068)) = E_1068
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_1067,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_3',E_1068),k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_4',E_1068)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1067))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_1067,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_3',E_1068),k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_4',E_1068)),u1_struct_0('#skF_1'),u1_struct_0(B_1067))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_1067,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_3',E_1068),k3_tmap_1('#skF_1',B_1067,'#skF_1','#skF_4',E_1068)))
      | ~ m1_subset_1(E_1068,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_1067))))
      | ~ v1_funct_2(E_1068,u1_struct_0('#skF_1'),u1_struct_0(B_1067))
      | ~ v1_funct_1(E_1068)
      | ~ l1_pre_topc(B_1067)
      | ~ v2_pre_topc(B_1067)
      | v2_struct_0(B_1067) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_52,c_48,c_5800])).

tff(c_10635,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_10593])).

tff(c_10665,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_42,c_40,c_38,c_7391,c_324,c_338,c_324,c_338,c_338,c_324,c_338,c_10635])).

tff(c_10666,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_10665])).

tff(c_10851,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10666])).

tff(c_10854,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1408,c_10851])).

tff(c_10858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_360,c_357,c_10854])).

tff(c_10859,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10666])).

tff(c_10884,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_10859])).

tff(c_10887,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_550,c_10884])).

tff(c_10890,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_363,c_360,c_357,c_386,c_383,c_380,c_10887])).

tff(c_10892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_10890])).

tff(c_10893,plain,(
    k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_10859])).

tff(c_36,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_65,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_11010,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10893,c_65])).

tff(c_11132,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_126,c_11010])).

tff(c_11135,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_11132])).

tff(c_11137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_11135])).
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
% 0.12/0.33  % DateTime   : Tue Dec  1 11:32:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.34/5.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.52/5.33  
% 13.52/5.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.52/5.33  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.52/5.33  
% 13.52/5.33  %Foreground sorts:
% 13.52/5.33  
% 13.52/5.33  
% 13.52/5.33  %Background operators:
% 13.52/5.33  
% 13.52/5.33  
% 13.52/5.33  %Foreground operators:
% 13.52/5.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.52/5.33  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.52/5.33  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 13.52/5.33  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 13.52/5.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.52/5.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.52/5.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.52/5.33  tff('#skF_5', type, '#skF_5': $i).
% 13.52/5.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.52/5.33  tff('#skF_2', type, '#skF_2': $i).
% 13.52/5.33  tff('#skF_3', type, '#skF_3': $i).
% 13.52/5.33  tff('#skF_1', type, '#skF_1': $i).
% 13.52/5.33  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 13.52/5.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.52/5.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.52/5.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.52/5.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.52/5.33  tff('#skF_4', type, '#skF_4': $i).
% 13.52/5.33  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 13.52/5.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.52/5.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 13.52/5.33  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.52/5.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.52/5.33  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 13.52/5.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.52/5.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.52/5.33  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 13.52/5.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.52/5.33  
% 13.52/5.36  tff(f_301, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k2_tmap_1(A, B, E, C), k2_tmap_1(A, B, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_tmap_1)).
% 13.52/5.36  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 13.52/5.36  tff(f_73, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 13.52/5.36  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 13.52/5.36  tff(f_196, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 13.52/5.36  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 13.52/5.36  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 13.52/5.36  tff(f_226, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 13.52/5.36  tff(f_174, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 13.52/5.36  tff(f_262, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_tmap_1)).
% 13.52/5.36  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 13.52/5.36  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.52/5.36  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_106, plain, (![D_148, B_149, E_153, F_152, C_150, A_151]: (r1_funct_2(A_151, B_149, C_150, D_148, E_153, E_153) | ~m1_subset_1(F_152, k1_zfmisc_1(k2_zfmisc_1(C_150, D_148))) | ~v1_funct_2(F_152, C_150, D_148) | ~v1_funct_1(F_152) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2(E_153, A_151, B_149) | ~v1_funct_1(E_153) | v1_xboole_0(D_148) | v1_xboole_0(B_149))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.52/5.36  tff(c_108, plain, (![A_151, B_149, E_153]: (r1_funct_2(A_151, B_149, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), E_153, E_153) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2(E_153, A_151, B_149) | ~v1_funct_1(E_153) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_149))), inference(resolution, [status(thm)], [c_38, c_106])).
% 13.52/5.36  tff(c_111, plain, (![A_151, B_149, E_153]: (r1_funct_2(A_151, B_149, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), E_153, E_153) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2(E_153, A_151, B_149) | ~v1_funct_1(E_153) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_149))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_108])).
% 13.52/5.36  tff(c_112, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_111])).
% 13.52/5.36  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.52/5.36  tff(c_115, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_112, c_8])).
% 13.52/5.36  tff(c_118, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_58, c_115])).
% 13.52/5.36  tff(c_121, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_118])).
% 13.52/5.36  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_121])).
% 13.52/5.36  tff(c_127, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_111])).
% 13.52/5.36  tff(c_126, plain, (![A_151, B_149, E_153]: (r1_funct_2(A_151, B_149, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), E_153, E_153) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_149))) | ~v1_funct_2(E_153, A_151, B_149) | ~v1_funct_1(E_153) | v1_xboole_0(B_149))), inference(splitRight, [status(thm)], [c_111])).
% 13.52/5.36  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_44, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_92, plain, (![A_141, B_142, C_143]: (m1_pre_topc(k1_tsep_1(A_141, B_142, C_143), A_141) | ~m1_pre_topc(C_143, A_141) | v2_struct_0(C_143) | ~m1_pre_topc(B_142, A_141) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_196])).
% 13.52/5.36  tff(c_95, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_44, c_92])).
% 13.52/5.36  tff(c_97, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_46, c_95])).
% 13.52/5.36  tff(c_98, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_97])).
% 13.52/5.36  tff(c_177, plain, (![E_181, A_182, C_183, D_185, B_184]: (k3_tmap_1(A_182, B_184, C_183, D_185, E_181)=k2_partfun1(u1_struct_0(C_183), u1_struct_0(B_184), E_181, u1_struct_0(D_185)) | ~m1_pre_topc(D_185, C_183) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_183), u1_struct_0(B_184)))) | ~v1_funct_2(E_181, u1_struct_0(C_183), u1_struct_0(B_184)) | ~v1_funct_1(E_181) | ~m1_pre_topc(D_185, A_182) | ~m1_pre_topc(C_183, A_182) | ~l1_pre_topc(B_184) | ~v2_pre_topc(B_184) | v2_struct_0(B_184) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.52/5.36  tff(c_181, plain, (![A_182, D_185]: (k3_tmap_1(A_182, '#skF_2', '#skF_1', D_185, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_185)) | ~m1_pre_topc(D_185, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_185, A_182) | ~m1_pre_topc('#skF_1', A_182) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_38, c_177])).
% 13.52/5.36  tff(c_185, plain, (![A_182, D_185]: (k3_tmap_1(A_182, '#skF_2', '#skF_1', D_185, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_185)) | ~m1_pre_topc(D_185, '#skF_1') | ~m1_pre_topc(D_185, A_182) | ~m1_pre_topc('#skF_1', A_182) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_181])).
% 13.52/5.36  tff(c_187, plain, (![A_186, D_187]: (k3_tmap_1(A_186, '#skF_2', '#skF_1', D_187, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_187)) | ~m1_pre_topc(D_187, '#skF_1') | ~m1_pre_topc(D_187, A_186) | ~m1_pre_topc('#skF_1', A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(negUnitSimplification, [status(thm)], [c_58, c_185])).
% 13.52/5.36  tff(c_195, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_50, c_187])).
% 13.52/5.36  tff(c_207, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_98, c_50, c_195])).
% 13.52/5.36  tff(c_208, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_207])).
% 13.52/5.36  tff(c_137, plain, (![A_164, B_165, C_166, D_167]: (k2_partfun1(u1_struct_0(A_164), u1_struct_0(B_165), C_166, u1_struct_0(D_167))=k2_tmap_1(A_164, B_165, C_166, D_167) | ~m1_pre_topc(D_167, A_164) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_164), u1_struct_0(B_165)))) | ~v1_funct_2(C_166, u1_struct_0(A_164), u1_struct_0(B_165)) | ~v1_funct_1(C_166) | ~l1_pre_topc(B_165) | ~v2_pre_topc(B_165) | v2_struct_0(B_165) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.52/5.36  tff(c_139, plain, (![D_167]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_167))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_167) | ~m1_pre_topc(D_167, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_137])).
% 13.52/5.36  tff(c_142, plain, (![D_167]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_167))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_167) | ~m1_pre_topc(D_167, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_42, c_40, c_139])).
% 13.52/5.36  tff(c_143, plain, (![D_167]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_167))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_167) | ~m1_pre_topc(D_167, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_142])).
% 13.52/5.36  tff(c_317, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_208, c_143])).
% 13.52/5.36  tff(c_324, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_317])).
% 13.52/5.36  tff(c_129, plain, (![C_158, B_159, D_157, A_161, E_160]: (v1_funct_1(k3_tmap_1(A_161, B_159, C_158, D_157, E_160)) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_158), u1_struct_0(B_159)))) | ~v1_funct_2(E_160, u1_struct_0(C_158), u1_struct_0(B_159)) | ~v1_funct_1(E_160) | ~m1_pre_topc(D_157, A_161) | ~m1_pre_topc(C_158, A_161) | ~l1_pre_topc(B_159) | ~v2_pre_topc(B_159) | v2_struct_0(B_159) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_226])).
% 13.52/5.36  tff(c_131, plain, (![A_161, D_157]: (v1_funct_1(k3_tmap_1(A_161, '#skF_2', '#skF_1', D_157, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_157, A_161) | ~m1_pre_topc('#skF_1', A_161) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(resolution, [status(thm)], [c_38, c_129])).
% 13.52/5.36  tff(c_134, plain, (![A_161, D_157]: (v1_funct_1(k3_tmap_1(A_161, '#skF_2', '#skF_1', D_157, '#skF_5')) | ~m1_pre_topc(D_157, A_161) | ~m1_pre_topc('#skF_1', A_161) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_131])).
% 13.52/5.36  tff(c_135, plain, (![A_161, D_157]: (v1_funct_1(k3_tmap_1(A_161, '#skF_2', '#skF_1', D_157, '#skF_5')) | ~m1_pre_topc(D_157, A_161) | ~m1_pre_topc('#skF_1', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_58, c_134])).
% 13.52/5.36  tff(c_352, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_324, c_135])).
% 13.52/5.36  tff(c_362, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_98, c_50, c_352])).
% 13.52/5.36  tff(c_363, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_362])).
% 13.52/5.36  tff(c_153, plain, (![C_170, D_169, B_171, A_173, E_172]: (v1_funct_2(k3_tmap_1(A_173, B_171, C_170, D_169, E_172), u1_struct_0(D_169), u1_struct_0(B_171)) | ~m1_subset_1(E_172, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170), u1_struct_0(B_171)))) | ~v1_funct_2(E_172, u1_struct_0(C_170), u1_struct_0(B_171)) | ~v1_funct_1(E_172) | ~m1_pre_topc(D_169, A_173) | ~m1_pre_topc(C_170, A_173) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_226])).
% 13.52/5.36  tff(c_155, plain, (![A_173, D_169]: (v1_funct_2(k3_tmap_1(A_173, '#skF_2', '#skF_1', D_169, '#skF_5'), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_169, A_173) | ~m1_pre_topc('#skF_1', A_173) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(resolution, [status(thm)], [c_38, c_153])).
% 13.52/5.36  tff(c_158, plain, (![A_173, D_169]: (v1_funct_2(k3_tmap_1(A_173, '#skF_2', '#skF_1', D_169, '#skF_5'), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_169, A_173) | ~m1_pre_topc('#skF_1', A_173) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_155])).
% 13.52/5.36  tff(c_159, plain, (![A_173, D_169]: (v1_funct_2(k3_tmap_1(A_173, '#skF_2', '#skF_1', D_169, '#skF_5'), u1_struct_0(D_169), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_169, A_173) | ~m1_pre_topc('#skF_1', A_173) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(negUnitSimplification, [status(thm)], [c_58, c_158])).
% 13.52/5.36  tff(c_349, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_324, c_159])).
% 13.52/5.36  tff(c_359, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_98, c_50, c_349])).
% 13.52/5.36  tff(c_360, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_359])).
% 13.52/5.36  tff(c_28, plain, (![E_72, C_70, B_69, D_71, A_68]: (m1_subset_1(k3_tmap_1(A_68, B_69, C_70, D_71, E_72), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71), u1_struct_0(B_69)))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_70), u1_struct_0(B_69)))) | ~v1_funct_2(E_72, u1_struct_0(C_70), u1_struct_0(B_69)) | ~v1_funct_1(E_72) | ~m1_pre_topc(D_71, A_68) | ~m1_pre_topc(C_70, A_68) | ~l1_pre_topc(B_69) | ~v2_pre_topc(B_69) | v2_struct_0(B_69) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_226])).
% 13.52/5.36  tff(c_346, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_324, c_28])).
% 13.52/5.36  tff(c_356, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_98, c_50, c_42, c_40, c_38, c_346])).
% 13.52/5.36  tff(c_357, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_356])).
% 13.52/5.36  tff(c_193, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_46, c_187])).
% 13.52/5.36  tff(c_203, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_98, c_46, c_193])).
% 13.52/5.36  tff(c_204, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_203])).
% 13.52/5.36  tff(c_331, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_204, c_143])).
% 13.52/5.36  tff(c_338, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_331])).
% 13.52/5.36  tff(c_375, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_338, c_135])).
% 13.52/5.36  tff(c_385, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_98, c_46, c_375])).
% 13.52/5.36  tff(c_386, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_385])).
% 13.52/5.36  tff(c_372, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_338, c_159])).
% 13.52/5.36  tff(c_382, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_98, c_46, c_372])).
% 13.52/5.36  tff(c_383, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_382])).
% 13.52/5.36  tff(c_369, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_338, c_28])).
% 13.52/5.36  tff(c_379, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_98, c_46, c_42, c_40, c_38, c_369])).
% 13.52/5.36  tff(c_380, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_379])).
% 13.52/5.36  tff(c_523, plain, (![C_200, E_205, F_203, D_204, B_202, A_201]: (m1_subset_1(k10_tmap_1(A_201, B_202, C_200, D_204, E_205, F_203), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_201, C_200, D_204)), u1_struct_0(B_202)))) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_204), u1_struct_0(B_202)))) | ~v1_funct_2(F_203, u1_struct_0(D_204), u1_struct_0(B_202)) | ~v1_funct_1(F_203) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_200), u1_struct_0(B_202)))) | ~v1_funct_2(E_205, u1_struct_0(C_200), u1_struct_0(B_202)) | ~v1_funct_1(E_205) | ~m1_pre_topc(D_204, A_201) | v2_struct_0(D_204) | ~m1_pre_topc(C_200, A_201) | v2_struct_0(C_200) | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | v2_struct_0(B_202) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.52/5.36  tff(c_540, plain, (![B_202, E_205, F_203]: (m1_subset_1(k10_tmap_1('#skF_1', B_202, '#skF_3', '#skF_4', E_205, F_203), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_202)))) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_202)))) | ~v1_funct_2(F_203, u1_struct_0('#skF_4'), u1_struct_0(B_202)) | ~v1_funct_1(F_203) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_202)))) | ~v1_funct_2(E_205, u1_struct_0('#skF_3'), u1_struct_0(B_202)) | ~v1_funct_1(E_205) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | v2_struct_0(B_202) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_523])).
% 13.52/5.36  tff(c_549, plain, (![B_202, E_205, F_203]: (m1_subset_1(k10_tmap_1('#skF_1', B_202, '#skF_3', '#skF_4', E_205, F_203), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_202)))) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_202)))) | ~v1_funct_2(F_203, u1_struct_0('#skF_4'), u1_struct_0(B_202)) | ~v1_funct_1(F_203) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_202)))) | ~v1_funct_2(E_205, u1_struct_0('#skF_3'), u1_struct_0(B_202)) | ~v1_funct_1(E_205) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | v2_struct_0(B_202) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_46, c_540])).
% 13.52/5.36  tff(c_550, plain, (![B_202, E_205, F_203]: (m1_subset_1(k10_tmap_1('#skF_1', B_202, '#skF_3', '#skF_4', E_205, F_203), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_202)))) | ~m1_subset_1(F_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_202)))) | ~v1_funct_2(F_203, u1_struct_0('#skF_4'), u1_struct_0(B_202)) | ~v1_funct_1(F_203) | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_202)))) | ~v1_funct_2(E_205, u1_struct_0('#skF_3'), u1_struct_0(B_202)) | ~v1_funct_1(E_205) | ~l1_pre_topc(B_202) | ~v2_pre_topc(B_202) | v2_struct_0(B_202))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_549])).
% 13.52/5.36  tff(c_388, plain, (![A_195, C_194, B_196, E_199, D_198, F_197]: (v1_funct_2(k10_tmap_1(A_195, B_196, C_194, D_198, E_199, F_197), u1_struct_0(k1_tsep_1(A_195, C_194, D_198)), u1_struct_0(B_196)) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_198), u1_struct_0(B_196)))) | ~v1_funct_2(F_197, u1_struct_0(D_198), u1_struct_0(B_196)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_194), u1_struct_0(B_196)))) | ~v1_funct_2(E_199, u1_struct_0(C_194), u1_struct_0(B_196)) | ~v1_funct_1(E_199) | ~m1_pre_topc(D_198, A_195) | v2_struct_0(D_198) | ~m1_pre_topc(C_194, A_195) | v2_struct_0(C_194) | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | v2_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.52/5.36  tff(c_391, plain, (![B_196, E_199, F_197]: (v1_funct_2(k10_tmap_1('#skF_1', B_196, '#skF_3', '#skF_4', E_199, F_197), u1_struct_0('#skF_1'), u1_struct_0(B_196)) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_196)))) | ~v1_funct_2(F_197, u1_struct_0('#skF_4'), u1_struct_0(B_196)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_196)))) | ~v1_funct_2(E_199, u1_struct_0('#skF_3'), u1_struct_0(B_196)) | ~v1_funct_1(E_199) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_388])).
% 13.52/5.36  tff(c_393, plain, (![B_196, E_199, F_197]: (v1_funct_2(k10_tmap_1('#skF_1', B_196, '#skF_3', '#skF_4', E_199, F_197), u1_struct_0('#skF_1'), u1_struct_0(B_196)) | ~m1_subset_1(F_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_196)))) | ~v1_funct_2(F_197, u1_struct_0('#skF_4'), u1_struct_0(B_196)) | ~v1_funct_1(F_197) | ~m1_subset_1(E_199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_196)))) | ~v1_funct_2(E_199, u1_struct_0('#skF_3'), u1_struct_0(B_196)) | ~v1_funct_1(E_199) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_196) | ~v2_pre_topc(B_196) | v2_struct_0(B_196) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_46, c_391])).
% 13.52/5.36  tff(c_1381, plain, (![B_260, E_261, F_262]: (v1_funct_2(k10_tmap_1('#skF_1', B_260, '#skF_3', '#skF_4', E_261, F_262), u1_struct_0('#skF_1'), u1_struct_0(B_260)) | ~m1_subset_1(F_262, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_260)))) | ~v1_funct_2(F_262, u1_struct_0('#skF_4'), u1_struct_0(B_260)) | ~v1_funct_1(F_262) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_260)))) | ~v1_funct_2(E_261, u1_struct_0('#skF_3'), u1_struct_0(B_260)) | ~v1_funct_1(E_261) | ~l1_pre_topc(B_260) | ~v2_pre_topc(B_260) | v2_struct_0(B_260))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_393])).
% 13.52/5.36  tff(c_1389, plain, (![E_261]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_261, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_261, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_261) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_380, c_1381])).
% 13.52/5.36  tff(c_1407, plain, (![E_261]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_261, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_261, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_261) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_386, c_383, c_1389])).
% 13.52/5.36  tff(c_1408, plain, (![E_261]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_261, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_261, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_261))), inference(negUnitSimplification, [status(thm)], [c_58, c_1407])).
% 13.52/5.36  tff(c_20, plain, (![F_64, D_62, A_59, C_61, E_63, B_60]: (v1_funct_1(k10_tmap_1(A_59, B_60, C_61, D_62, E_63, F_64)) | ~m1_subset_1(F_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62), u1_struct_0(B_60)))) | ~v1_funct_2(F_64, u1_struct_0(D_62), u1_struct_0(B_60)) | ~v1_funct_1(F_64) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0(B_60)))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0(B_60)) | ~v1_funct_1(E_63) | ~m1_pre_topc(D_62, A_59) | v2_struct_0(D_62) | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc(B_60) | ~v2_pre_topc(B_60) | v2_struct_0(B_60) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.52/5.36  tff(c_398, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_380, c_20])).
% 13.52/5.36  tff(c_413, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_386, c_383, c_398])).
% 13.52/5.36  tff(c_1554, plain, (![A_274, C_275, E_276]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', C_275, '#skF_4', E_276, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_275), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_276, u1_struct_0(C_275), u1_struct_0('#skF_2')) | ~v1_funct_1(E_276) | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc(C_275, A_274) | v2_struct_0(C_275) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_58, c_48, c_413])).
% 13.52/5.36  tff(c_1580, plain, (![A_274]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc('#skF_3', A_274) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_357, c_1554])).
% 13.52/5.36  tff(c_1633, plain, (![A_274]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc('#skF_3', A_274) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_360, c_1580])).
% 13.52/5.36  tff(c_1634, plain, (![A_274]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc('#skF_3', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_52, c_1633])).
% 13.52/5.36  tff(c_1476, plain, (![B_267, E_268, F_269]: (m1_subset_1(k10_tmap_1('#skF_1', B_267, '#skF_3', '#skF_4', E_268, F_269), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_267)))) | ~m1_subset_1(F_269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_267)))) | ~v1_funct_2(F_269, u1_struct_0('#skF_4'), u1_struct_0(B_267)) | ~v1_funct_1(F_269) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_267)))) | ~v1_funct_2(E_268, u1_struct_0('#skF_3'), u1_struct_0(B_267)) | ~v1_funct_1(E_268) | ~l1_pre_topc(B_267) | ~v2_pre_topc(B_267) | v2_struct_0(B_267))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_549])).
% 13.52/5.36  tff(c_247, plain, (![D_192, E_193, C_188, B_190, F_191, A_189]: (v1_funct_1(k10_tmap_1(A_189, B_190, C_188, D_192, E_193, F_191)) | ~m1_subset_1(F_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_192), u1_struct_0(B_190)))) | ~v1_funct_2(F_191, u1_struct_0(D_192), u1_struct_0(B_190)) | ~v1_funct_1(F_191) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188), u1_struct_0(B_190)))) | ~v1_funct_2(E_193, u1_struct_0(C_188), u1_struct_0(B_190)) | ~v1_funct_1(E_193) | ~m1_pre_topc(D_192, A_189) | v2_struct_0(D_192) | ~m1_pre_topc(C_188, A_189) | v2_struct_0(C_188) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.52/5.36  tff(c_251, plain, (![A_189, C_188, E_193]: (v1_funct_1(k10_tmap_1(A_189, '#skF_2', C_188, '#skF_1', E_193, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_193, u1_struct_0(C_188), u1_struct_0('#skF_2')) | ~v1_funct_1(E_193) | ~m1_pre_topc('#skF_1', A_189) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_188, A_189) | v2_struct_0(C_188) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(resolution, [status(thm)], [c_38, c_247])).
% 13.52/5.36  tff(c_255, plain, (![A_189, C_188, E_193]: (v1_funct_1(k10_tmap_1(A_189, '#skF_2', C_188, '#skF_1', E_193, '#skF_5')) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_193, u1_struct_0(C_188), u1_struct_0('#skF_2')) | ~v1_funct_1(E_193) | ~m1_pre_topc('#skF_1', A_189) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_188, A_189) | v2_struct_0(C_188) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_251])).
% 13.52/5.36  tff(c_256, plain, (![A_189, C_188, E_193]: (v1_funct_1(k10_tmap_1(A_189, '#skF_2', C_188, '#skF_1', E_193, '#skF_5')) | ~m1_subset_1(E_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_188), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_193, u1_struct_0(C_188), u1_struct_0('#skF_2')) | ~v1_funct_1(E_193) | ~m1_pre_topc('#skF_1', A_189) | ~m1_pre_topc(C_188, A_189) | v2_struct_0(C_188) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(negUnitSimplification, [status(thm)], [c_58, c_64, c_255])).
% 13.52/5.36  tff(c_1479, plain, (![A_189, E_268, F_269]: (v1_funct_1(k10_tmap_1(A_189, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_268, F_269), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_268, F_269), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_268, F_269)) | ~m1_pre_topc('#skF_1', A_189) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189) | ~m1_subset_1(F_269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_269, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_269) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_268, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_268) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1476, c_256])).
% 13.52/5.36  tff(c_1496, plain, (![A_189, E_268, F_269]: (v1_funct_1(k10_tmap_1(A_189, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_268, F_269), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_268, F_269), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_268, F_269)) | ~m1_pre_topc('#skF_1', A_189) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189) | ~m1_subset_1(F_269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_269, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_269) | ~m1_subset_1(E_268, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_268, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_268) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1479])).
% 13.52/5.36  tff(c_7312, plain, (![A_811, E_812, F_813]: (v1_funct_1(k10_tmap_1(A_811, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_812, F_813), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_812, F_813), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_812, F_813)) | ~m1_pre_topc('#skF_1', A_811) | ~l1_pre_topc(A_811) | ~v2_pre_topc(A_811) | v2_struct_0(A_811) | ~m1_subset_1(F_813, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_813, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_813) | ~m1_subset_1(E_812, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_812, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_812))), inference(negUnitSimplification, [status(thm)], [c_58, c_64, c_1496])).
% 13.52/5.36  tff(c_7314, plain, (![A_811, E_261]: (v1_funct_1(k10_tmap_1(A_811, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_261, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_261, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_811) | ~l1_pre_topc(A_811) | ~v2_pre_topc(A_811) | v2_struct_0(A_811) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_261, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_261))), inference(resolution, [status(thm)], [c_1408, c_7312])).
% 13.52/5.36  tff(c_7355, plain, (![A_823, E_824]: (v1_funct_1(k10_tmap_1(A_823, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_824, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_824, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_823) | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823) | ~m1_subset_1(E_824, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_824, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_824))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_383, c_380, c_7314])).
% 13.52/5.36  tff(c_7363, plain, (![A_823]: (v1_funct_1(k10_tmap_1(A_823, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_823) | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')))), inference(resolution, [status(thm)], [c_357, c_7355])).
% 13.52/5.36  tff(c_7376, plain, (![A_823]: (v1_funct_1(k10_tmap_1(A_823, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_823) | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_360, c_7363])).
% 13.52/5.36  tff(c_7381, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_7376])).
% 13.52/5.36  tff(c_7384, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1634, c_7381])).
% 13.52/5.36  tff(c_7387, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_46, c_7384])).
% 13.52/5.36  tff(c_7389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_7387])).
% 13.52/5.36  tff(c_7391, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_7376])).
% 13.52/5.36  tff(c_573, plain, (![B_226, E_223, C_224, D_225, A_227]: (r2_funct_2(u1_struct_0(k1_tsep_1(A_227, C_224, D_225)), u1_struct_0(B_226), E_223, k10_tmap_1(A_227, B_226, C_224, D_225, k3_tmap_1(A_227, B_226, k1_tsep_1(A_227, C_224, D_225), C_224, E_223), k3_tmap_1(A_227, B_226, k1_tsep_1(A_227, C_224, D_225), D_225, E_223))) | ~m1_subset_1(E_223, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_227, C_224, D_225)), u1_struct_0(B_226)))) | ~v1_funct_2(E_223, u1_struct_0(k1_tsep_1(A_227, C_224, D_225)), u1_struct_0(B_226)) | ~v1_funct_1(E_223) | ~m1_pre_topc(D_225, A_227) | v2_struct_0(D_225) | ~m1_pre_topc(C_224, A_227) | v2_struct_0(C_224) | ~l1_pre_topc(B_226) | ~v2_pre_topc(B_226) | v2_struct_0(B_226) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_262])).
% 13.52/5.36  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.52/5.36  tff(c_5773, plain, (![A_715, D_713, B_712, C_714, E_711]: (k10_tmap_1(A_715, B_712, C_714, D_713, k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), C_714, E_711), k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), D_713, E_711))=E_711 | ~m1_subset_1(k10_tmap_1(A_715, B_712, C_714, D_713, k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), C_714, E_711), k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), D_713, E_711)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_715, C_714, D_713)), u1_struct_0(B_712)))) | ~v1_funct_2(k10_tmap_1(A_715, B_712, C_714, D_713, k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), C_714, E_711), k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), D_713, E_711)), u1_struct_0(k1_tsep_1(A_715, C_714, D_713)), u1_struct_0(B_712)) | ~v1_funct_1(k10_tmap_1(A_715, B_712, C_714, D_713, k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), C_714, E_711), k3_tmap_1(A_715, B_712, k1_tsep_1(A_715, C_714, D_713), D_713, E_711))) | ~m1_subset_1(E_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_715, C_714, D_713)), u1_struct_0(B_712)))) | ~v1_funct_2(E_711, u1_struct_0(k1_tsep_1(A_715, C_714, D_713)), u1_struct_0(B_712)) | ~v1_funct_1(E_711) | ~m1_pre_topc(D_713, A_715) | v2_struct_0(D_713) | ~m1_pre_topc(C_714, A_715) | v2_struct_0(C_714) | ~l1_pre_topc(B_712) | ~v2_pre_topc(B_712) | v2_struct_0(B_712) | ~l1_pre_topc(A_715) | ~v2_pre_topc(A_715) | v2_struct_0(A_715))), inference(resolution, [status(thm)], [c_573, c_4])).
% 13.52/5.36  tff(c_5791, plain, (![B_712, E_711]: (k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_711))=E_711 | ~m1_subset_1(k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_4', E_711)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_712)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_711)), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_712)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_711))) | ~m1_subset_1(E_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_712)))) | ~v1_funct_2(E_711, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_712)) | ~v1_funct_1(E_711) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_712) | ~v2_pre_topc(B_712) | v2_struct_0(B_712) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_5773])).
% 13.52/5.36  tff(c_5800, plain, (![B_712, E_711]: (k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_4', E_711))=E_711 | ~m1_subset_1(k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_4', E_711)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_712)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_4', E_711)), u1_struct_0('#skF_1'), u1_struct_0(B_712)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_712, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_3', E_711), k3_tmap_1('#skF_1', B_712, '#skF_1', '#skF_4', E_711))) | ~m1_subset_1(E_711, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_712)))) | ~v1_funct_2(E_711, u1_struct_0('#skF_1'), u1_struct_0(B_712)) | ~v1_funct_1(E_711) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_712) | ~v2_pre_topc(B_712) | v2_struct_0(B_712) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_50, c_46, c_44, c_44, c_44, c_44, c_44, c_44, c_44, c_44, c_44, c_44, c_44, c_5791])).
% 13.52/5.36  tff(c_10593, plain, (![B_1067, E_1068]: (k10_tmap_1('#skF_1', B_1067, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_3', E_1068), k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_4', E_1068))=E_1068 | ~m1_subset_1(k10_tmap_1('#skF_1', B_1067, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_3', E_1068), k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_4', E_1068)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1067)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_1067, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_3', E_1068), k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_4', E_1068)), u1_struct_0('#skF_1'), u1_struct_0(B_1067)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_1067, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_3', E_1068), k3_tmap_1('#skF_1', B_1067, '#skF_1', '#skF_4', E_1068))) | ~m1_subset_1(E_1068, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_1067)))) | ~v1_funct_2(E_1068, u1_struct_0('#skF_1'), u1_struct_0(B_1067)) | ~v1_funct_1(E_1068) | ~l1_pre_topc(B_1067) | ~v2_pre_topc(B_1067) | v2_struct_0(B_1067))), inference(negUnitSimplification, [status(thm)], [c_64, c_52, c_48, c_5800])).
% 13.52/5.36  tff(c_10635, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_324, c_10593])).
% 13.52/5.36  tff(c_10665, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_42, c_40, c_38, c_7391, c_324, c_338, c_324, c_338, c_338, c_324, c_338, c_10635])).
% 13.52/5.36  tff(c_10666, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_10665])).
% 13.52/5.36  tff(c_10851, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_10666])).
% 13.52/5.36  tff(c_10854, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_1408, c_10851])).
% 13.52/5.36  tff(c_10858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_363, c_360, c_357, c_10854])).
% 13.52/5.36  tff(c_10859, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_10666])).
% 13.52/5.36  tff(c_10884, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_10859])).
% 13.52/5.36  tff(c_10887, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_550, c_10884])).
% 13.52/5.36  tff(c_10890, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_363, c_360, c_357, c_386, c_383, c_380, c_10887])).
% 13.52/5.36  tff(c_10892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_10890])).
% 13.52/5.36  tff(c_10893, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_10859])).
% 13.52/5.36  tff(c_36, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_301])).
% 13.52/5.36  tff(c_65, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 13.52/5.36  tff(c_11010, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10893, c_65])).
% 13.52/5.36  tff(c_11132, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_126, c_11010])).
% 13.52/5.36  tff(c_11135, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_11132])).
% 13.52/5.36  tff(c_11137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_11135])).
% 13.52/5.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.52/5.36  
% 13.52/5.36  Inference rules
% 13.52/5.36  ----------------------
% 13.52/5.36  #Ref     : 0
% 13.52/5.36  #Sup     : 2045
% 13.52/5.36  #Fact    : 0
% 13.52/5.36  #Define  : 0
% 13.52/5.36  #Split   : 40
% 13.52/5.36  #Chain   : 0
% 13.52/5.36  #Close   : 0
% 13.52/5.36  
% 13.52/5.36  Ordering : KBO
% 13.52/5.36  
% 13.52/5.36  Simplification rules
% 13.52/5.36  ----------------------
% 13.52/5.36  #Subsume      : 1931
% 13.52/5.36  #Demod        : 6316
% 13.52/5.36  #Tautology    : 280
% 13.52/5.36  #SimpNegUnit  : 1040
% 13.52/5.36  #BackRed      : 46
% 13.52/5.36  
% 13.52/5.36  #Partial instantiations: 0
% 13.52/5.36  #Strategies tried      : 1
% 13.52/5.36  
% 13.52/5.36  Timing (in seconds)
% 13.52/5.36  ----------------------
% 13.52/5.36  Preprocessing        : 0.41
% 13.52/5.36  Parsing              : 0.23
% 13.52/5.36  CNF conversion       : 0.04
% 13.52/5.36  Main loop            : 4.13
% 13.52/5.36  Inferencing          : 1.17
% 13.52/5.36  Reduction            : 1.51
% 13.52/5.36  Demodulation         : 1.21
% 13.52/5.36  BG Simplification    : 0.08
% 13.52/5.36  Subsumption          : 1.23
% 13.52/5.36  Abstraction          : 0.17
% 13.52/5.36  MUC search           : 0.00
% 13.52/5.36  Cooper               : 0.00
% 13.52/5.36  Total                : 4.61
% 13.52/5.36  Index Insertion      : 0.00
% 13.52/5.36  Index Deletion       : 0.00
% 13.52/5.36  Index Matching       : 0.00
% 13.52/5.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
