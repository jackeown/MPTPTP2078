%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:10 EST 2020

% Result     : Theorem 13.59s
% Output     : CNFRefutation 13.59s
% Verified   : 
% Statistics : Number of formulae       :  190 (11171 expanded)
%              Number of leaves         :   38 (4426 expanded)
%              Depth                    :   30
%              Number of atoms          : 1080 (86754 expanded)
%              Number of equality atoms :   35 (6425 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_295,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r1_funct_2)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_244,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_204,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_240,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_123,plain,(
    ! [C_154,A_155,E_157,B_153,D_152,F_156] :
      ( r1_funct_2(A_155,B_153,C_154,D_152,E_157,E_157)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(C_154,D_152)))
      | ~ v1_funct_2(F_156,C_154,D_152)
      | ~ v1_funct_1(F_156)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_153)))
      | ~ v1_funct_2(E_157,A_155,B_153)
      | ~ v1_funct_1(E_157)
      | v1_xboole_0(D_152)
      | v1_xboole_0(B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_125,plain,(
    ! [A_155,B_153,E_157] :
      ( r1_funct_2(A_155,B_153,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_157,E_157)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_153)))
      | ~ v1_funct_2(E_157,A_155,B_153)
      | ~ v1_funct_1(E_157)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_153) ) ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_128,plain,(
    ! [A_155,B_153,E_157] :
      ( r1_funct_2(A_155,B_153,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),E_157,E_157)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_153)))
      | ~ v1_funct_2(E_157,A_155,B_153)
      | ~ v1_funct_1(E_157)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_125])).

tff(c_129,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(u1_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_132,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_129,c_8])).

tff(c_135,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_132])).

tff(c_138,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_138])).

tff(c_144,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_30,plain,(
    ! [A_101] :
      ( m1_pre_topc(A_101,A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_194,plain,(
    ! [C_187,B_188,E_185,D_189,A_186] :
      ( k3_tmap_1(A_186,B_188,C_187,D_189,E_185) = k2_partfun1(u1_struct_0(C_187),u1_struct_0(B_188),E_185,u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,C_187)
      | ~ m1_subset_1(E_185,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187),u1_struct_0(B_188))))
      | ~ v1_funct_2(E_185,u1_struct_0(C_187),u1_struct_0(B_188))
      | ~ v1_funct_1(E_185)
      | ~ m1_pre_topc(D_189,A_186)
      | ~ m1_pre_topc(C_187,A_186)
      | ~ l1_pre_topc(B_188)
      | ~ v2_pre_topc(B_188)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_198,plain,(
    ! [A_186,D_189] :
      ( k3_tmap_1(A_186,'#skF_2','#skF_1',D_189,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_189,A_186)
      | ~ m1_pre_topc('#skF_1',A_186)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_36,c_194])).

tff(c_202,plain,(
    ! [A_186,D_189] :
      ( k3_tmap_1(A_186,'#skF_2','#skF_1',D_189,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_189))
      | ~ m1_pre_topc(D_189,'#skF_1')
      | ~ m1_pre_topc(D_189,A_186)
      | ~ m1_pre_topc('#skF_1',A_186)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_198])).

tff(c_204,plain,(
    ! [A_190,D_191] :
      ( k3_tmap_1(A_190,'#skF_2','#skF_1',D_191,'#skF_5') = k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_191))
      | ~ m1_pre_topc(D_191,'#skF_1')
      | ~ m1_pre_topc(D_191,A_190)
      | ~ m1_pre_topc('#skF_1',A_190)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_202])).

tff(c_210,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_204])).

tff(c_219,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_210])).

tff(c_220,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_219])).

tff(c_225,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_228,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_225])).

tff(c_232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_228])).

tff(c_234,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_212,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_204])).

tff(c_223,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_44,c_212])).

tff(c_224,plain,
    ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_223])).

tff(c_463,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_224])).

tff(c_154,plain,(
    ! [A_168,B_169,C_170,D_171] :
      ( k2_partfun1(u1_struct_0(A_168),u1_struct_0(B_169),C_170,u1_struct_0(D_171)) = k2_tmap_1(A_168,B_169,C_170,D_171)
      | ~ m1_pre_topc(D_171,A_168)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168),u1_struct_0(B_169))))
      | ~ v1_funct_2(C_170,u1_struct_0(A_168),u1_struct_0(B_169))
      | ~ v1_funct_1(C_170)
      | ~ l1_pre_topc(B_169)
      | ~ v2_pre_topc(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_156,plain,(
    ! [D_171] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_171)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171)
      | ~ m1_pre_topc(D_171,'#skF_1')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_154])).

tff(c_159,plain,(
    ! [D_171] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_171)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171)
      | ~ m1_pre_topc(D_171,'#skF_1')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_40,c_38,c_156])).

tff(c_160,plain,(
    ! [D_171] :
      ( k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_171)) = k2_tmap_1('#skF_1','#skF_2','#skF_5',D_171)
      | ~ m1_pre_topc(D_171,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_159])).

tff(c_467,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_160])).

tff(c_474,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_467])).

tff(c_146,plain,(
    ! [C_162,E_165,D_161,B_163,A_164] :
      ( v1_funct_1(k3_tmap_1(A_164,B_163,C_162,D_161,E_165))
      | ~ m1_subset_1(E_165,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162),u1_struct_0(B_163))))
      | ~ v1_funct_2(E_165,u1_struct_0(C_162),u1_struct_0(B_163))
      | ~ v1_funct_1(E_165)
      | ~ m1_pre_topc(D_161,A_164)
      | ~ m1_pre_topc(C_162,A_164)
      | ~ l1_pre_topc(B_163)
      | ~ v2_pre_topc(B_163)
      | v2_struct_0(B_163)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_148,plain,(
    ! [A_164,D_161] :
      ( v1_funct_1(k3_tmap_1(A_164,'#skF_2','#skF_1',D_161,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_161,A_164)
      | ~ m1_pre_topc('#skF_1',A_164)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_36,c_146])).

tff(c_151,plain,(
    ! [A_164,D_161] :
      ( v1_funct_1(k3_tmap_1(A_164,'#skF_2','#skF_1',D_161,'#skF_5'))
      | ~ m1_pre_topc(D_161,A_164)
      | ~ m1_pre_topc('#skF_1',A_164)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_148])).

tff(c_152,plain,(
    ! [A_164,D_161] :
      ( v1_funct_1(k3_tmap_1(A_164,'#skF_2','#skF_1',D_161,'#skF_5'))
      | ~ m1_pre_topc(D_161,A_164)
      | ~ m1_pre_topc('#skF_1',A_164)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_151])).

tff(c_488,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_152])).

tff(c_498,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_234,c_44,c_488])).

tff(c_499,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_498])).

tff(c_170,plain,(
    ! [D_173,E_177,A_176,B_175,C_174] :
      ( v1_funct_2(k3_tmap_1(A_176,B_175,C_174,D_173,E_177),u1_struct_0(D_173),u1_struct_0(B_175))
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_174),u1_struct_0(B_175))))
      | ~ v1_funct_2(E_177,u1_struct_0(C_174),u1_struct_0(B_175))
      | ~ v1_funct_1(E_177)
      | ~ m1_pre_topc(D_173,A_176)
      | ~ m1_pre_topc(C_174,A_176)
      | ~ l1_pre_topc(B_175)
      | ~ v2_pre_topc(B_175)
      | v2_struct_0(B_175)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_172,plain,(
    ! [A_176,D_173] :
      ( v1_funct_2(k3_tmap_1(A_176,'#skF_2','#skF_1',D_173,'#skF_5'),u1_struct_0(D_173),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_173,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_175,plain,(
    ! [A_176,D_173] :
      ( v1_funct_2(k3_tmap_1(A_176,'#skF_2','#skF_1',D_173,'#skF_5'),u1_struct_0(D_173),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_173,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_172])).

tff(c_176,plain,(
    ! [A_176,D_173] :
      ( v1_funct_2(k3_tmap_1(A_176,'#skF_2','#skF_1',D_173,'#skF_5'),u1_struct_0(D_173),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_173,A_176)
      | ~ m1_pre_topc('#skF_1',A_176)
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_175])).

tff(c_485,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_176])).

tff(c_495,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_234,c_44,c_485])).

tff(c_496,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_495])).

tff(c_22,plain,(
    ! [B_66,A_65,C_67,D_68,E_69] :
      ( m1_subset_1(k3_tmap_1(A_65,B_66,C_67,D_68,E_69),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_68),u1_struct_0(B_66))))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67),u1_struct_0(B_66))))
      | ~ v1_funct_2(E_69,u1_struct_0(C_67),u1_struct_0(B_66))
      | ~ v1_funct_1(E_69)
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc(C_67,A_65)
      | ~ l1_pre_topc(B_66)
      | ~ v2_pre_topc(B_66)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_482,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_474,c_22])).

tff(c_492,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_234,c_44,c_40,c_38,c_36,c_482])).

tff(c_493,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_492])).

tff(c_26,plain,(
    ! [B_66,A_65,C_67,D_68,E_69] :
      ( v1_funct_1(k3_tmap_1(A_65,B_66,C_67,D_68,E_69))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67),u1_struct_0(B_66))))
      | ~ v1_funct_2(E_69,u1_struct_0(C_67),u1_struct_0(B_66))
      | ~ v1_funct_1(E_69)
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc(C_67,A_65)
      | ~ l1_pre_topc(B_66)
      | ~ v2_pre_topc(B_66)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_511,plain,(
    ! [A_65,D_68] :
      ( v1_funct_1(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_493,c_26])).

tff(c_534,plain,(
    ! [A_65,D_68] :
      ( v1_funct_1(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_499,c_496,c_511])).

tff(c_535,plain,(
    ! [A_65,D_68] :
      ( v1_funct_1(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_534])).

tff(c_24,plain,(
    ! [B_66,A_65,C_67,D_68,E_69] :
      ( v1_funct_2(k3_tmap_1(A_65,B_66,C_67,D_68,E_69),u1_struct_0(D_68),u1_struct_0(B_66))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67),u1_struct_0(B_66))))
      | ~ v1_funct_2(E_69,u1_struct_0(C_67),u1_struct_0(B_66))
      | ~ v1_funct_1(E_69)
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc(C_67,A_65)
      | ~ l1_pre_topc(B_66)
      | ~ v2_pre_topc(B_66)
      | v2_struct_0(B_66)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_507,plain,(
    ! [A_65,D_68] :
      ( v1_funct_2(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_68),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_493,c_24])).

tff(c_526,plain,(
    ! [A_65,D_68] :
      ( v1_funct_2(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_68),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_499,c_496,c_507])).

tff(c_527,plain,(
    ! [A_65,D_68] :
      ( v1_funct_2(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0(D_68),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_526])).

tff(c_178,plain,(
    ! [E_184,C_181,A_183,B_182,D_180] :
      ( m1_subset_1(k3_tmap_1(A_183,B_182,C_181,D_180,E_184),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_180),u1_struct_0(B_182))))
      | ~ m1_subset_1(E_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_181),u1_struct_0(B_182))))
      | ~ v1_funct_2(E_184,u1_struct_0(C_181),u1_struct_0(B_182))
      | ~ v1_funct_1(E_184)
      | ~ m1_pre_topc(D_180,A_183)
      | ~ m1_pre_topc(C_181,A_183)
      | ~ l1_pre_topc(B_182)
      | ~ v2_pre_topc(B_182)
      | v2_struct_0(B_182)
      | ~ l1_pre_topc(A_183)
      | ~ v2_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_10,plain,(
    ! [D_10,A_7,F_12,B_8,E_11,C_9] :
      ( r1_funct_2(A_7,B_8,C_9,D_10,E_11,E_11)
      | ~ m1_subset_1(F_12,k1_zfmisc_1(k2_zfmisc_1(C_9,D_10)))
      | ~ v1_funct_2(F_12,C_9,D_10)
      | ~ v1_funct_1(F_12)
      | ~ m1_subset_1(E_11,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(E_11,A_7,B_8)
      | ~ v1_funct_1(E_11)
      | v1_xboole_0(D_10)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2467,plain,(
    ! [B_312,B_311,D_309,A_310,E_315,C_314,E_316,A_313] :
      ( r1_funct_2(A_313,B_311,u1_struct_0(D_309),u1_struct_0(B_312),E_315,E_315)
      | ~ v1_funct_2(k3_tmap_1(A_310,B_312,C_314,D_309,E_316),u1_struct_0(D_309),u1_struct_0(B_312))
      | ~ v1_funct_1(k3_tmap_1(A_310,B_312,C_314,D_309,E_316))
      | ~ m1_subset_1(E_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_311)))
      | ~ v1_funct_2(E_315,A_313,B_311)
      | ~ v1_funct_1(E_315)
      | v1_xboole_0(u1_struct_0(B_312))
      | v1_xboole_0(B_311)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314),u1_struct_0(B_312))))
      | ~ v1_funct_2(E_316,u1_struct_0(C_314),u1_struct_0(B_312))
      | ~ v1_funct_1(E_316)
      | ~ m1_pre_topc(D_309,A_310)
      | ~ m1_pre_topc(C_314,A_310)
      | ~ l1_pre_topc(B_312)
      | ~ v2_pre_topc(B_312)
      | v2_struct_0(B_312)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310) ) ),
    inference(resolution,[status(thm)],[c_178,c_10])).

tff(c_2481,plain,(
    ! [A_65,B_311,D_68,E_315,A_313] :
      ( r1_funct_2(A_313,B_311,u1_struct_0(D_68),u1_struct_0('#skF_2'),E_315,E_315)
      | ~ v1_funct_1(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_311)))
      | ~ v1_funct_2(E_315,A_313,B_311)
      | ~ v1_funct_1(E_315)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_311)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_527,c_2467])).

tff(c_2514,plain,(
    ! [A_65,B_311,D_68,E_315,A_313] :
      ( r1_funct_2(A_313,B_311,u1_struct_0(D_68),u1_struct_0('#skF_2'),E_315,E_315)
      | ~ v1_funct_1(k3_tmap_1(A_65,'#skF_2','#skF_4',D_68,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_311)))
      | ~ v1_funct_2(E_315,A_313,B_311)
      | ~ v1_funct_1(E_315)
      | v1_xboole_0(u1_struct_0('#skF_2'))
      | v1_xboole_0(B_311)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_68,A_65)
      | ~ m1_pre_topc('#skF_4',A_65)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_499,c_496,c_493,c_2481])).

tff(c_4486,plain,(
    ! [E_536,A_540,A_538,D_537,B_539] :
      ( r1_funct_2(A_540,B_539,u1_struct_0(D_537),u1_struct_0('#skF_2'),E_536,E_536)
      | ~ v1_funct_1(k3_tmap_1(A_538,'#skF_2','#skF_4',D_537,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_536,k1_zfmisc_1(k2_zfmisc_1(A_540,B_539)))
      | ~ v1_funct_2(E_536,A_540,B_539)
      | ~ v1_funct_1(E_536)
      | v1_xboole_0(B_539)
      | ~ m1_pre_topc(D_537,A_538)
      | ~ m1_pre_topc('#skF_4',A_538)
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538)
      | v2_struct_0(A_538) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_144,c_2514])).

tff(c_4492,plain,(
    ! [E_542,A_543,B_544,A_545,D_541] :
      ( r1_funct_2(A_545,B_544,u1_struct_0(D_541),u1_struct_0('#skF_2'),E_542,E_542)
      | ~ m1_subset_1(E_542,k1_zfmisc_1(k2_zfmisc_1(A_545,B_544)))
      | ~ v1_funct_2(E_542,A_545,B_544)
      | ~ v1_funct_1(E_542)
      | v1_xboole_0(B_544)
      | ~ m1_pre_topc(D_541,A_543)
      | ~ m1_pre_topc('#skF_4',A_543)
      | ~ l1_pre_topc(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(resolution,[status(thm)],[c_535,c_4486])).

tff(c_4508,plain,(
    ! [A_545,B_544,A_101,E_542] :
      ( r1_funct_2(A_545,B_544,u1_struct_0(A_101),u1_struct_0('#skF_2'),E_542,E_542)
      | ~ m1_subset_1(E_542,k1_zfmisc_1(k2_zfmisc_1(A_545,B_544)))
      | ~ v1_funct_2(E_542,A_545,B_544)
      | ~ v1_funct_1(E_542)
      | v1_xboole_0(B_544)
      | ~ m1_pre_topc('#skF_4',A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_30,c_4492])).

tff(c_233,plain,(
    k2_partfun1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_258,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_160])).

tff(c_265,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5') = k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_258])).

tff(c_279,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_152])).

tff(c_289,plain,
    ( v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_234,c_48,c_279])).

tff(c_290,plain,(
    v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_289])).

tff(c_276,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_176])).

tff(c_286,plain,
    ( v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_234,c_48,c_276])).

tff(c_287,plain,(
    v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_286])).

tff(c_273,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_265,c_22])).

tff(c_283,plain,
    ( m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_234,c_48,c_40,c_38,c_36,c_273])).

tff(c_284,plain,(
    m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_283])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_42,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_543,plain,(
    ! [C_204,D_208,A_205,E_209,F_207,B_206] :
      ( m1_subset_1(k10_tmap_1(A_205,B_206,C_204,D_208,E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_205,C_204,D_208)),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_208),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0(D_208),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0(C_204),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | ~ m1_pre_topc(D_208,A_205)
      | v2_struct_0(D_208)
      | ~ m1_pre_topc(C_204,A_205)
      | v2_struct_0(C_204)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_560,plain,(
    ! [B_206,E_209,F_207] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_543])).

tff(c_569,plain,(
    ! [B_206,E_209,F_207] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_560])).

tff(c_570,plain,(
    ! [B_206,E_209,F_207] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_206,'#skF_3','#skF_4',E_209,F_207),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_206))))
      | ~ m1_subset_1(F_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_206))))
      | ~ v1_funct_2(F_207,u1_struct_0('#skF_4'),u1_struct_0(B_206))
      | ~ v1_funct_1(F_207)
      | ~ m1_subset_1(E_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_206))))
      | ~ v1_funct_2(E_209,u1_struct_0('#skF_3'),u1_struct_0(B_206))
      | ~ v1_funct_1(E_209)
      | ~ l1_pre_topc(B_206)
      | ~ v2_pre_topc(B_206)
      | v2_struct_0(B_206) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_569])).

tff(c_397,plain,(
    ! [B_200,C_198,F_201,E_203,D_202,A_199] :
      ( v1_funct_2(k10_tmap_1(A_199,B_200,C_198,D_202,E_203,F_201),u1_struct_0(k1_tsep_1(A_199,C_198,D_202)),u1_struct_0(B_200))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_202),u1_struct_0(B_200))))
      | ~ v1_funct_2(F_201,u1_struct_0(D_202),u1_struct_0(B_200))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_198),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_203,u1_struct_0(C_198),u1_struct_0(B_200))
      | ~ v1_funct_1(E_203)
      | ~ m1_pre_topc(D_202,A_199)
      | v2_struct_0(D_202)
      | ~ m1_pre_topc(C_198,A_199)
      | v2_struct_0(C_198)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_400,plain,(
    ! [B_200,E_203,F_201] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_200,'#skF_3','#skF_4',E_203,F_201),u1_struct_0('#skF_1'),u1_struct_0(B_200))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_200))))
      | ~ v1_funct_2(F_201,u1_struct_0('#skF_4'),u1_struct_0(B_200))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_203,u1_struct_0('#skF_3'),u1_struct_0(B_200))
      | ~ v1_funct_1(E_203)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_397])).

tff(c_402,plain,(
    ! [B_200,E_203,F_201] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_200,'#skF_3','#skF_4',E_203,F_201),u1_struct_0('#skF_1'),u1_struct_0(B_200))
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_200))))
      | ~ v1_funct_2(F_201,u1_struct_0('#skF_4'),u1_struct_0(B_200))
      | ~ v1_funct_1(F_201)
      | ~ m1_subset_1(E_203,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))))
      | ~ v1_funct_2(E_203,u1_struct_0('#skF_3'),u1_struct_0(B_200))
      | ~ v1_funct_1(E_203)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_400])).

tff(c_1189,plain,(
    ! [B_263,E_264,F_265] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_263,'#skF_3','#skF_4',E_264,F_265),u1_struct_0('#skF_1'),u1_struct_0(B_263))
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_263))))
      | ~ v1_funct_2(F_265,u1_struct_0('#skF_4'),u1_struct_0(B_263))
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_263))))
      | ~ v1_funct_2(E_264,u1_struct_0('#skF_3'),u1_struct_0(B_263))
      | ~ v1_funct_1(E_264)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_402])).

tff(c_1200,plain,(
    ! [E_264] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_264,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_264,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_264)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_493,c_1189])).

tff(c_1218,plain,(
    ! [E_264] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_264,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_264,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_264)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_499,c_496,c_1200])).

tff(c_1219,plain,(
    ! [E_264] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_264,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_264,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_264) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1218])).

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

tff(c_503,plain,(
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
    inference(resolution,[status(thm)],[c_493,c_20])).

tff(c_518,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_499,c_496,c_503])).

tff(c_2347,plain,(
    ! [A_301,C_302,E_303] :
      ( v1_funct_1(k10_tmap_1(A_301,'#skF_2',C_302,'#skF_4',E_303,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_subset_1(E_303,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_302),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_303,u1_struct_0(C_302),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_303)
      | ~ m1_pre_topc('#skF_4',A_301)
      | ~ m1_pre_topc(C_302,A_301)
      | v2_struct_0(C_302)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_46,c_518])).

tff(c_2391,plain,(
    ! [A_301] :
      ( v1_funct_1(k10_tmap_1(A_301,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
      | ~ m1_pre_topc('#skF_4',A_301)
      | ~ m1_pre_topc('#skF_3',A_301)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(resolution,[status(thm)],[c_284,c_2347])).

tff(c_2449,plain,(
    ! [A_301] :
      ( v1_funct_1(k10_tmap_1(A_301,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_301)
      | ~ m1_pre_topc('#skF_3',A_301)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_287,c_2391])).

tff(c_2450,plain,(
    ! [A_301] :
      ( v1_funct_1(k10_tmap_1(A_301,'#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_301)
      | ~ m1_pre_topc('#skF_3',A_301)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301)
      | v2_struct_0(A_301) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2449])).

tff(c_1387,plain,(
    ! [B_272,E_273,F_274] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_272,'#skF_3','#skF_4',E_273,F_274),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_272))))
      | ~ m1_subset_1(F_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_272))))
      | ~ v1_funct_2(F_274,u1_struct_0('#skF_4'),u1_struct_0(B_272))
      | ~ v1_funct_1(F_274)
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_272))))
      | ~ v1_funct_2(E_273,u1_struct_0('#skF_3'),u1_struct_0(B_272))
      | ~ v1_funct_1(E_273)
      | ~ l1_pre_topc(B_272)
      | ~ v2_pre_topc(B_272)
      | v2_struct_0(B_272) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_569])).

tff(c_292,plain,(
    ! [E_197,B_194,D_196,F_195,A_193,C_192] :
      ( v1_funct_1(k10_tmap_1(A_193,B_194,C_192,D_196,E_197,F_195))
      | ~ m1_subset_1(F_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_196),u1_struct_0(B_194))))
      | ~ v1_funct_2(F_195,u1_struct_0(D_196),u1_struct_0(B_194))
      | ~ v1_funct_1(F_195)
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0(B_194))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0(B_194))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc(D_196,A_193)
      | v2_struct_0(D_196)
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | ~ l1_pre_topc(B_194)
      | ~ v2_pre_topc(B_194)
      | v2_struct_0(B_194)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_296,plain,(
    ! [A_193,C_192,E_197] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2',C_192,'#skF_1',E_197,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(resolution,[status(thm)],[c_36,c_292])).

tff(c_300,plain,(
    ! [A_193,C_192,E_197] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2',C_192,'#skF_1',E_197,'#skF_5'))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_296])).

tff(c_301,plain,(
    ! [A_193,C_192,E_197] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2',C_192,'#skF_1',E_197,'#skF_5'))
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_197,u1_struct_0(C_192),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_197)
      | ~ m1_pre_topc('#skF_1',A_193)
      | ~ m1_pre_topc(C_192,A_193)
      | v2_struct_0(C_192)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_300])).

tff(c_1390,plain,(
    ! [A_193,E_273,F_274] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_273,F_274),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_273,F_274),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_273,F_274))
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193)
      | ~ m1_subset_1(F_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_274,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_274)
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_273,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_273)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1387,c_301])).

tff(c_1407,plain,(
    ! [A_193,E_273,F_274] :
      ( v1_funct_1(k10_tmap_1(A_193,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_273,F_274),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_273,F_274),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_273,F_274))
      | ~ m1_pre_topc('#skF_1',A_193)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | v2_struct_0(A_193)
      | ~ m1_subset_1(F_274,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_274,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_274)
      | ~ m1_subset_1(E_273,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_273,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_273)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1390])).

tff(c_7290,plain,(
    ! [A_753,E_754,F_755] :
      ( v1_funct_1(k10_tmap_1(A_753,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_754,F_755),'#skF_5'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_754,F_755),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_754,F_755))
      | ~ m1_pre_topc('#skF_1',A_753)
      | ~ l1_pre_topc(A_753)
      | ~ v2_pre_topc(A_753)
      | v2_struct_0(A_753)
      | ~ m1_subset_1(F_755,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(F_755,u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(F_755)
      | ~ m1_subset_1(E_754,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_754,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_754) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_1407])).

tff(c_7292,plain,(
    ! [A_753,E_264] :
      ( v1_funct_1(k10_tmap_1(A_753,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_264,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_264,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_753)
      | ~ l1_pre_topc(A_753)
      | ~ v2_pre_topc(A_753)
      | v2_struct_0(A_753)
      | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_264,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_264) ) ),
    inference(resolution,[status(thm)],[c_1219,c_7290])).

tff(c_7986,plain,(
    ! [A_788,E_789] :
      ( v1_funct_1(k10_tmap_1(A_788,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_789,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_789,k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_788)
      | ~ l1_pre_topc(A_788)
      | ~ v2_pre_topc(A_788)
      | v2_struct_0(A_788)
      | ~ m1_subset_1(E_789,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_789,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_789) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_496,c_493,c_7292])).

tff(c_8024,plain,(
    ! [A_788] :
      ( v1_funct_1(k10_tmap_1(A_788,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_788)
      | ~ l1_pre_topc(A_788)
      | ~ v2_pre_topc(A_788)
      | v2_struct_0(A_788)
      | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_284,c_7986])).

tff(c_8069,plain,(
    ! [A_788] :
      ( v1_funct_1(k10_tmap_1(A_788,'#skF_2','#skF_1','#skF_1',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),'#skF_5'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')))
      | ~ m1_pre_topc('#skF_1',A_788)
      | ~ l1_pre_topc(A_788)
      | ~ v2_pre_topc(A_788)
      | v2_struct_0(A_788) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_287,c_8024])).

tff(c_8074,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_8069])).

tff(c_8077,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2450,c_8074])).

tff(c_8080,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_8077])).

tff(c_8082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_8080])).

tff(c_8084,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_8069])).

tff(c_626,plain,(
    ! [B_221,D_225,E_224,C_223,A_222] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(A_222,C_223,D_225)),u1_struct_0(B_221),E_224,k10_tmap_1(A_222,B_221,C_223,D_225,k3_tmap_1(A_222,B_221,k1_tsep_1(A_222,C_223,D_225),C_223,E_224),k3_tmap_1(A_222,B_221,k1_tsep_1(A_222,C_223,D_225),D_225,E_224)))
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_222,C_223,D_225)),u1_struct_0(B_221))))
      | ~ v1_funct_2(E_224,u1_struct_0(k1_tsep_1(A_222,C_223,D_225)),u1_struct_0(B_221))
      | ~ v1_funct_1(E_224)
      | ~ m1_pre_topc(D_225,A_222)
      | v2_struct_0(D_225)
      | ~ m1_pre_topc(C_223,A_222)
      | v2_struct_0(C_223)
      | ~ l1_pre_topc(B_221)
      | ~ v2_pre_topc(B_221)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

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

tff(c_6086,plain,(
    ! [E_659,C_658,B_661,D_660,A_662] :
      ( k10_tmap_1(A_662,B_661,C_658,D_660,k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),C_658,E_659),k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),D_660,E_659)) = E_659
      | ~ m1_subset_1(k10_tmap_1(A_662,B_661,C_658,D_660,k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),C_658,E_659),k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),D_660,E_659)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_662,C_658,D_660)),u1_struct_0(B_661))))
      | ~ v1_funct_2(k10_tmap_1(A_662,B_661,C_658,D_660,k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),C_658,E_659),k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),D_660,E_659)),u1_struct_0(k1_tsep_1(A_662,C_658,D_660)),u1_struct_0(B_661))
      | ~ v1_funct_1(k10_tmap_1(A_662,B_661,C_658,D_660,k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),C_658,E_659),k3_tmap_1(A_662,B_661,k1_tsep_1(A_662,C_658,D_660),D_660,E_659)))
      | ~ m1_subset_1(E_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_662,C_658,D_660)),u1_struct_0(B_661))))
      | ~ v1_funct_2(E_659,u1_struct_0(k1_tsep_1(A_662,C_658,D_660)),u1_struct_0(B_661))
      | ~ v1_funct_1(E_659)
      | ~ m1_pre_topc(D_660,A_662)
      | v2_struct_0(D_660)
      | ~ m1_pre_topc(C_658,A_662)
      | v2_struct_0(C_658)
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | v2_struct_0(B_661)
      | ~ l1_pre_topc(A_662)
      | ~ v2_pre_topc(A_662)
      | v2_struct_0(A_662) ) ),
    inference(resolution,[status(thm)],[c_626,c_4])).

tff(c_6101,plain,(
    ! [B_661,E_659] :
      ( k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_659),k3_tmap_1('#skF_1',B_661,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_659)) = E_659
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_3',E_659),k3_tmap_1('#skF_1',B_661,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_659)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_661))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_659),k3_tmap_1('#skF_1',B_661,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_659)),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_661))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_659),k3_tmap_1('#skF_1',B_661,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_659)))
      | ~ m1_subset_1(E_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_661))))
      | ~ v1_funct_2(E_659,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_661))
      | ~ v1_funct_1(E_659)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | v2_struct_0(B_661)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_6086])).

tff(c_6110,plain,(
    ! [B_661,E_659] :
      ( k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_3',E_659),k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_4',E_659)) = E_659
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_3',E_659),k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_4',E_659)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_661))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_3',E_659),k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_4',E_659)),u1_struct_0('#skF_1'),u1_struct_0(B_661))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_661,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_3',E_659),k3_tmap_1('#skF_1',B_661,'#skF_1','#skF_4',E_659)))
      | ~ m1_subset_1(E_659,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_661))))
      | ~ v1_funct_2(E_659,u1_struct_0('#skF_1'),u1_struct_0(B_661))
      | ~ v1_funct_1(E_659)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_661)
      | ~ v2_pre_topc(B_661)
      | v2_struct_0(B_661)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48,c_44,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_42,c_6101])).

tff(c_11432,plain,(
    ! [B_998,E_999] :
      ( k10_tmap_1('#skF_1',B_998,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_3',E_999),k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_4',E_999)) = E_999
      | ~ m1_subset_1(k10_tmap_1('#skF_1',B_998,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_3',E_999),k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_4',E_999)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_998))))
      | ~ v1_funct_2(k10_tmap_1('#skF_1',B_998,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_3',E_999),k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_4',E_999)),u1_struct_0('#skF_1'),u1_struct_0(B_998))
      | ~ v1_funct_1(k10_tmap_1('#skF_1',B_998,'#skF_3','#skF_4',k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_3',E_999),k3_tmap_1('#skF_1',B_998,'#skF_1','#skF_4',E_999)))
      | ~ m1_subset_1(E_999,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_998))))
      | ~ v1_funct_2(E_999,u1_struct_0('#skF_1'),u1_struct_0(B_998))
      | ~ v1_funct_1(E_999)
      | ~ l1_pre_topc(B_998)
      | ~ v2_pre_topc(B_998)
      | v2_struct_0(B_998) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_50,c_46,c_6110])).

tff(c_11471,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3','#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_11432])).

tff(c_11501,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_40,c_38,c_36,c_8084,c_265,c_474,c_265,c_474,c_265,c_265,c_474,c_11471])).

tff(c_11502,plain,
    ( k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5'
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_11501])).

tff(c_11522,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_11502])).

tff(c_11525,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1219,c_11522])).

tff(c_11529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_287,c_284,c_11525])).

tff(c_11530,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11502])).

tff(c_11584,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_11530])).

tff(c_11587,plain,
    ( ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))
    | ~ m1_subset_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_570,c_11584])).

tff(c_11590,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_290,c_287,c_284,c_499,c_496,c_493,c_11587])).

tff(c_11592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_11590])).

tff(c_11593,plain,(
    k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_11530])).

tff(c_34,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_295])).

tff(c_63,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_3'),k2_tmap_1('#skF_1','#skF_2','#skF_5','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34])).

tff(c_11600,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11593,c_63])).

tff(c_11728,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4508,c_11600])).

tff(c_11740,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_44,c_40,c_38,c_36,c_11728])).

tff(c_11742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_144,c_11740])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.59/5.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.59/5.46  
% 13.59/5.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.59/5.47  %$ r1_funct_2 > r2_funct_2 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.59/5.47  
% 13.59/5.47  %Foreground sorts:
% 13.59/5.47  
% 13.59/5.47  
% 13.59/5.47  %Background operators:
% 13.59/5.47  
% 13.59/5.47  
% 13.59/5.47  %Foreground operators:
% 13.59/5.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 13.59/5.47  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.59/5.47  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 13.59/5.47  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 13.59/5.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.59/5.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.59/5.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 13.59/5.47  tff('#skF_5', type, '#skF_5': $i).
% 13.59/5.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.59/5.47  tff('#skF_2', type, '#skF_2': $i).
% 13.59/5.47  tff('#skF_3', type, '#skF_3': $i).
% 13.59/5.47  tff('#skF_1', type, '#skF_1': $i).
% 13.59/5.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.59/5.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 13.59/5.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.59/5.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.59/5.47  tff('#skF_4', type, '#skF_4': $i).
% 13.59/5.47  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 13.59/5.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.59/5.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 13.59/5.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.59/5.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 13.59/5.47  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 13.59/5.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 13.59/5.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.59/5.47  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 13.59/5.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.59/5.47  
% 13.59/5.50  tff(f_295, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => r1_funct_2(u1_struct_0(A), u1_struct_0(B), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k2_tmap_1(A, B, E, C), k2_tmap_1(A, B, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_tmap_1)).
% 13.59/5.50  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 13.59/5.50  tff(f_73, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => r1_funct_2(A, B, C, D, E, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r1_funct_2)).
% 13.59/5.50  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 13.59/5.50  tff(f_244, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 13.59/5.50  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 13.59/5.50  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 13.59/5.50  tff(f_204, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 13.59/5.50  tff(f_174, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 13.59/5.50  tff(f_240, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B), E, k10_tmap_1(A, B, C, D, k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_tmap_1)).
% 13.59/5.50  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 13.59/5.50  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.59/5.50  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_123, plain, (![C_154, A_155, E_157, B_153, D_152, F_156]: (r1_funct_2(A_155, B_153, C_154, D_152, E_157, E_157) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(C_154, D_152))) | ~v1_funct_2(F_156, C_154, D_152) | ~v1_funct_1(F_156) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_153))) | ~v1_funct_2(E_157, A_155, B_153) | ~v1_funct_1(E_157) | v1_xboole_0(D_152) | v1_xboole_0(B_153))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.59/5.50  tff(c_125, plain, (![A_155, B_153, E_157]: (r1_funct_2(A_155, B_153, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), E_157, E_157) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_153))) | ~v1_funct_2(E_157, A_155, B_153) | ~v1_funct_1(E_157) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_153))), inference(resolution, [status(thm)], [c_36, c_123])).
% 13.59/5.50  tff(c_128, plain, (![A_155, B_153, E_157]: (r1_funct_2(A_155, B_153, u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), E_157, E_157) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_153))) | ~v1_funct_2(E_157, A_155, B_153) | ~v1_funct_1(E_157) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_153))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_125])).
% 13.59/5.50  tff(c_129, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_128])).
% 13.59/5.50  tff(c_8, plain, (![A_6]: (~v1_xboole_0(u1_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.59/5.50  tff(c_132, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_129, c_8])).
% 13.59/5.50  tff(c_135, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_132])).
% 13.59/5.50  tff(c_138, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_135])).
% 13.59/5.50  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_138])).
% 13.59/5.50  tff(c_144, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_128])).
% 13.59/5.50  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_30, plain, (![A_101]: (m1_pre_topc(A_101, A_101) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_244])).
% 13.59/5.50  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_194, plain, (![C_187, B_188, E_185, D_189, A_186]: (k3_tmap_1(A_186, B_188, C_187, D_189, E_185)=k2_partfun1(u1_struct_0(C_187), u1_struct_0(B_188), E_185, u1_struct_0(D_189)) | ~m1_pre_topc(D_189, C_187) | ~m1_subset_1(E_185, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_187), u1_struct_0(B_188)))) | ~v1_funct_2(E_185, u1_struct_0(C_187), u1_struct_0(B_188)) | ~v1_funct_1(E_185) | ~m1_pre_topc(D_189, A_186) | ~m1_pre_topc(C_187, A_186) | ~l1_pre_topc(B_188) | ~v2_pre_topc(B_188) | v2_struct_0(B_188) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_132])).
% 13.59/5.50  tff(c_198, plain, (![A_186, D_189]: (k3_tmap_1(A_186, '#skF_2', '#skF_1', D_189, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_189)) | ~m1_pre_topc(D_189, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_189, A_186) | ~m1_pre_topc('#skF_1', A_186) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(resolution, [status(thm)], [c_36, c_194])).
% 13.59/5.50  tff(c_202, plain, (![A_186, D_189]: (k3_tmap_1(A_186, '#skF_2', '#skF_1', D_189, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_189)) | ~m1_pre_topc(D_189, '#skF_1') | ~m1_pre_topc(D_189, A_186) | ~m1_pre_topc('#skF_1', A_186) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_198])).
% 13.59/5.50  tff(c_204, plain, (![A_190, D_191]: (k3_tmap_1(A_190, '#skF_2', '#skF_1', D_191, '#skF_5')=k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_191)) | ~m1_pre_topc(D_191, '#skF_1') | ~m1_pre_topc(D_191, A_190) | ~m1_pre_topc('#skF_1', A_190) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(negUnitSimplification, [status(thm)], [c_56, c_202])).
% 13.59/5.50  tff(c_210, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_204])).
% 13.59/5.50  tff(c_219, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_210])).
% 13.59/5.50  tff(c_220, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_219])).
% 13.59/5.50  tff(c_225, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_220])).
% 13.59/5.50  tff(c_228, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_225])).
% 13.59/5.50  tff(c_232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_228])).
% 13.59/5.50  tff(c_234, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_220])).
% 13.59/5.50  tff(c_212, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_204])).
% 13.59/5.50  tff(c_223, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_44, c_212])).
% 13.59/5.50  tff(c_224, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_223])).
% 13.59/5.50  tff(c_463, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_234, c_224])).
% 13.59/5.50  tff(c_154, plain, (![A_168, B_169, C_170, D_171]: (k2_partfun1(u1_struct_0(A_168), u1_struct_0(B_169), C_170, u1_struct_0(D_171))=k2_tmap_1(A_168, B_169, C_170, D_171) | ~m1_pre_topc(D_171, A_168) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_168), u1_struct_0(B_169)))) | ~v1_funct_2(C_170, u1_struct_0(A_168), u1_struct_0(B_169)) | ~v1_funct_1(C_170) | ~l1_pre_topc(B_169) | ~v2_pre_topc(B_169) | v2_struct_0(B_169) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.59/5.50  tff(c_156, plain, (![D_171]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_171))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171) | ~m1_pre_topc(D_171, '#skF_1') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_154])).
% 13.59/5.50  tff(c_159, plain, (![D_171]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_171))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171) | ~m1_pre_topc(D_171, '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_40, c_38, c_156])).
% 13.59/5.50  tff(c_160, plain, (![D_171]: (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_171))=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', D_171) | ~m1_pre_topc(D_171, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_159])).
% 13.59/5.50  tff(c_467, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_463, c_160])).
% 13.59/5.50  tff(c_474, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_467])).
% 13.59/5.50  tff(c_146, plain, (![C_162, E_165, D_161, B_163, A_164]: (v1_funct_1(k3_tmap_1(A_164, B_163, C_162, D_161, E_165)) | ~m1_subset_1(E_165, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_162), u1_struct_0(B_163)))) | ~v1_funct_2(E_165, u1_struct_0(C_162), u1_struct_0(B_163)) | ~v1_funct_1(E_165) | ~m1_pre_topc(D_161, A_164) | ~m1_pre_topc(C_162, A_164) | ~l1_pre_topc(B_163) | ~v2_pre_topc(B_163) | v2_struct_0(B_163) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_204])).
% 13.59/5.50  tff(c_148, plain, (![A_164, D_161]: (v1_funct_1(k3_tmap_1(A_164, '#skF_2', '#skF_1', D_161, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_161, A_164) | ~m1_pre_topc('#skF_1', A_164) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_36, c_146])).
% 13.59/5.50  tff(c_151, plain, (![A_164, D_161]: (v1_funct_1(k3_tmap_1(A_164, '#skF_2', '#skF_1', D_161, '#skF_5')) | ~m1_pre_topc(D_161, A_164) | ~m1_pre_topc('#skF_1', A_164) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_148])).
% 13.59/5.50  tff(c_152, plain, (![A_164, D_161]: (v1_funct_1(k3_tmap_1(A_164, '#skF_2', '#skF_1', D_161, '#skF_5')) | ~m1_pre_topc(D_161, A_164) | ~m1_pre_topc('#skF_1', A_164) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(negUnitSimplification, [status(thm)], [c_56, c_151])).
% 13.59/5.50  tff(c_488, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_474, c_152])).
% 13.59/5.50  tff(c_498, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_234, c_44, c_488])).
% 13.59/5.50  tff(c_499, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_498])).
% 13.59/5.50  tff(c_170, plain, (![D_173, E_177, A_176, B_175, C_174]: (v1_funct_2(k3_tmap_1(A_176, B_175, C_174, D_173, E_177), u1_struct_0(D_173), u1_struct_0(B_175)) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_174), u1_struct_0(B_175)))) | ~v1_funct_2(E_177, u1_struct_0(C_174), u1_struct_0(B_175)) | ~v1_funct_1(E_177) | ~m1_pre_topc(D_173, A_176) | ~m1_pre_topc(C_174, A_176) | ~l1_pre_topc(B_175) | ~v2_pre_topc(B_175) | v2_struct_0(B_175) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_204])).
% 13.59/5.50  tff(c_172, plain, (![A_176, D_173]: (v1_funct_2(k3_tmap_1(A_176, '#skF_2', '#skF_1', D_173, '#skF_5'), u1_struct_0(D_173), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_173, A_176) | ~m1_pre_topc('#skF_1', A_176) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_36, c_170])).
% 13.59/5.50  tff(c_175, plain, (![A_176, D_173]: (v1_funct_2(k3_tmap_1(A_176, '#skF_2', '#skF_1', D_173, '#skF_5'), u1_struct_0(D_173), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_173, A_176) | ~m1_pre_topc('#skF_1', A_176) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_172])).
% 13.59/5.50  tff(c_176, plain, (![A_176, D_173]: (v1_funct_2(k3_tmap_1(A_176, '#skF_2', '#skF_1', D_173, '#skF_5'), u1_struct_0(D_173), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_173, A_176) | ~m1_pre_topc('#skF_1', A_176) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(negUnitSimplification, [status(thm)], [c_56, c_175])).
% 13.59/5.50  tff(c_485, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_474, c_176])).
% 13.59/5.50  tff(c_495, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_234, c_44, c_485])).
% 13.59/5.50  tff(c_496, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_495])).
% 13.59/5.50  tff(c_22, plain, (![B_66, A_65, C_67, D_68, E_69]: (m1_subset_1(k3_tmap_1(A_65, B_66, C_67, D_68, E_69), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_68), u1_struct_0(B_66)))) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67), u1_struct_0(B_66)))) | ~v1_funct_2(E_69, u1_struct_0(C_67), u1_struct_0(B_66)) | ~v1_funct_1(E_69) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc(C_67, A_65) | ~l1_pre_topc(B_66) | ~v2_pre_topc(B_66) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_204])).
% 13.59/5.50  tff(c_482, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_474, c_22])).
% 13.59/5.50  tff(c_492, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_234, c_44, c_40, c_38, c_36, c_482])).
% 13.59/5.50  tff(c_493, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_492])).
% 13.59/5.50  tff(c_26, plain, (![B_66, A_65, C_67, D_68, E_69]: (v1_funct_1(k3_tmap_1(A_65, B_66, C_67, D_68, E_69)) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67), u1_struct_0(B_66)))) | ~v1_funct_2(E_69, u1_struct_0(C_67), u1_struct_0(B_66)) | ~v1_funct_1(E_69) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc(C_67, A_65) | ~l1_pre_topc(B_66) | ~v2_pre_topc(B_66) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_204])).
% 13.59/5.50  tff(c_511, plain, (![A_65, D_68]: (v1_funct_1(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_493, c_26])).
% 13.59/5.50  tff(c_534, plain, (![A_65, D_68]: (v1_funct_1(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_499, c_496, c_511])).
% 13.59/5.50  tff(c_535, plain, (![A_65, D_68]: (v1_funct_1(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(negUnitSimplification, [status(thm)], [c_56, c_534])).
% 13.59/5.50  tff(c_24, plain, (![B_66, A_65, C_67, D_68, E_69]: (v1_funct_2(k3_tmap_1(A_65, B_66, C_67, D_68, E_69), u1_struct_0(D_68), u1_struct_0(B_66)) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_67), u1_struct_0(B_66)))) | ~v1_funct_2(E_69, u1_struct_0(C_67), u1_struct_0(B_66)) | ~v1_funct_1(E_69) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc(C_67, A_65) | ~l1_pre_topc(B_66) | ~v2_pre_topc(B_66) | v2_struct_0(B_66) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_204])).
% 13.59/5.50  tff(c_507, plain, (![A_65, D_68]: (v1_funct_2(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_68), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_493, c_24])).
% 13.59/5.50  tff(c_526, plain, (![A_65, D_68]: (v1_funct_2(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_68), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_499, c_496, c_507])).
% 13.59/5.50  tff(c_527, plain, (![A_65, D_68]: (v1_funct_2(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0(D_68), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(negUnitSimplification, [status(thm)], [c_56, c_526])).
% 13.59/5.50  tff(c_178, plain, (![E_184, C_181, A_183, B_182, D_180]: (m1_subset_1(k3_tmap_1(A_183, B_182, C_181, D_180, E_184), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_180), u1_struct_0(B_182)))) | ~m1_subset_1(E_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_181), u1_struct_0(B_182)))) | ~v1_funct_2(E_184, u1_struct_0(C_181), u1_struct_0(B_182)) | ~v1_funct_1(E_184) | ~m1_pre_topc(D_180, A_183) | ~m1_pre_topc(C_181, A_183) | ~l1_pre_topc(B_182) | ~v2_pre_topc(B_182) | v2_struct_0(B_182) | ~l1_pre_topc(A_183) | ~v2_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_204])).
% 13.59/5.50  tff(c_10, plain, (![D_10, A_7, F_12, B_8, E_11, C_9]: (r1_funct_2(A_7, B_8, C_9, D_10, E_11, E_11) | ~m1_subset_1(F_12, k1_zfmisc_1(k2_zfmisc_1(C_9, D_10))) | ~v1_funct_2(F_12, C_9, D_10) | ~v1_funct_1(F_12) | ~m1_subset_1(E_11, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(E_11, A_7, B_8) | ~v1_funct_1(E_11) | v1_xboole_0(D_10) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_73])).
% 13.59/5.50  tff(c_2467, plain, (![B_312, B_311, D_309, A_310, E_315, C_314, E_316, A_313]: (r1_funct_2(A_313, B_311, u1_struct_0(D_309), u1_struct_0(B_312), E_315, E_315) | ~v1_funct_2(k3_tmap_1(A_310, B_312, C_314, D_309, E_316), u1_struct_0(D_309), u1_struct_0(B_312)) | ~v1_funct_1(k3_tmap_1(A_310, B_312, C_314, D_309, E_316)) | ~m1_subset_1(E_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_311))) | ~v1_funct_2(E_315, A_313, B_311) | ~v1_funct_1(E_315) | v1_xboole_0(u1_struct_0(B_312)) | v1_xboole_0(B_311) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314), u1_struct_0(B_312)))) | ~v1_funct_2(E_316, u1_struct_0(C_314), u1_struct_0(B_312)) | ~v1_funct_1(E_316) | ~m1_pre_topc(D_309, A_310) | ~m1_pre_topc(C_314, A_310) | ~l1_pre_topc(B_312) | ~v2_pre_topc(B_312) | v2_struct_0(B_312) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310))), inference(resolution, [status(thm)], [c_178, c_10])).
% 13.59/5.50  tff(c_2481, plain, (![A_65, B_311, D_68, E_315, A_313]: (r1_funct_2(A_313, B_311, u1_struct_0(D_68), u1_struct_0('#skF_2'), E_315, E_315) | ~v1_funct_1(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_311))) | ~v1_funct_2(E_315, A_313, B_311) | ~v1_funct_1(E_315) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_311) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_527, c_2467])).
% 13.59/5.50  tff(c_2514, plain, (![A_65, B_311, D_68, E_315, A_313]: (r1_funct_2(A_313, B_311, u1_struct_0(D_68), u1_struct_0('#skF_2'), E_315, E_315) | ~v1_funct_1(k3_tmap_1(A_65, '#skF_2', '#skF_4', D_68, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_311))) | ~v1_funct_2(E_315, A_313, B_311) | ~v1_funct_1(E_315) | v1_xboole_0(u1_struct_0('#skF_2')) | v1_xboole_0(B_311) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_68, A_65) | ~m1_pre_topc('#skF_4', A_65) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_499, c_496, c_493, c_2481])).
% 13.59/5.50  tff(c_4486, plain, (![E_536, A_540, A_538, D_537, B_539]: (r1_funct_2(A_540, B_539, u1_struct_0(D_537), u1_struct_0('#skF_2'), E_536, E_536) | ~v1_funct_1(k3_tmap_1(A_538, '#skF_2', '#skF_4', D_537, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_536, k1_zfmisc_1(k2_zfmisc_1(A_540, B_539))) | ~v1_funct_2(E_536, A_540, B_539) | ~v1_funct_1(E_536) | v1_xboole_0(B_539) | ~m1_pre_topc(D_537, A_538) | ~m1_pre_topc('#skF_4', A_538) | ~l1_pre_topc(A_538) | ~v2_pre_topc(A_538) | v2_struct_0(A_538))), inference(negUnitSimplification, [status(thm)], [c_56, c_144, c_2514])).
% 13.59/5.50  tff(c_4492, plain, (![E_542, A_543, B_544, A_545, D_541]: (r1_funct_2(A_545, B_544, u1_struct_0(D_541), u1_struct_0('#skF_2'), E_542, E_542) | ~m1_subset_1(E_542, k1_zfmisc_1(k2_zfmisc_1(A_545, B_544))) | ~v1_funct_2(E_542, A_545, B_544) | ~v1_funct_1(E_542) | v1_xboole_0(B_544) | ~m1_pre_topc(D_541, A_543) | ~m1_pre_topc('#skF_4', A_543) | ~l1_pre_topc(A_543) | ~v2_pre_topc(A_543) | v2_struct_0(A_543))), inference(resolution, [status(thm)], [c_535, c_4486])).
% 13.59/5.50  tff(c_4508, plain, (![A_545, B_544, A_101, E_542]: (r1_funct_2(A_545, B_544, u1_struct_0(A_101), u1_struct_0('#skF_2'), E_542, E_542) | ~m1_subset_1(E_542, k1_zfmisc_1(k2_zfmisc_1(A_545, B_544))) | ~v1_funct_2(E_542, A_545, B_544) | ~v1_funct_1(E_542) | v1_xboole_0(B_544) | ~m1_pre_topc('#skF_4', A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_30, c_4492])).
% 13.59/5.50  tff(c_233, plain, (k2_partfun1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_220])).
% 13.59/5.50  tff(c_258, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_233, c_160])).
% 13.59/5.50  tff(c_265, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5')=k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_258])).
% 13.59/5.50  tff(c_279, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_265, c_152])).
% 13.59/5.50  tff(c_289, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_234, c_48, c_279])).
% 13.59/5.50  tff(c_290, plain, (v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_289])).
% 13.59/5.50  tff(c_276, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_265, c_176])).
% 13.59/5.50  tff(c_286, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_234, c_48, c_276])).
% 13.59/5.50  tff(c_287, plain, (v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_286])).
% 13.59/5.50  tff(c_273, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_265, c_22])).
% 13.59/5.50  tff(c_283, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_234, c_48, c_40, c_38, c_36, c_273])).
% 13.59/5.50  tff(c_284, plain, (m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_283])).
% 13.59/5.50  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_42, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_543, plain, (![C_204, D_208, A_205, E_209, F_207, B_206]: (m1_subset_1(k10_tmap_1(A_205, B_206, C_204, D_208, E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_205, C_204, D_208)), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_208), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0(D_208), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_204), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0(C_204), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | ~m1_pre_topc(D_208, A_205) | v2_struct_0(D_208) | ~m1_pre_topc(C_204, A_205) | v2_struct_0(C_204) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.59/5.50  tff(c_560, plain, (![B_206, E_209, F_207]: (m1_subset_1(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_543])).
% 13.59/5.50  tff(c_569, plain, (![B_206, E_209, F_207]: (m1_subset_1(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_560])).
% 13.59/5.50  tff(c_570, plain, (![B_206, E_209, F_207]: (m1_subset_1(k10_tmap_1('#skF_1', B_206, '#skF_3', '#skF_4', E_209, F_207), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_206)))) | ~m1_subset_1(F_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_206)))) | ~v1_funct_2(F_207, u1_struct_0('#skF_4'), u1_struct_0(B_206)) | ~v1_funct_1(F_207) | ~m1_subset_1(E_209, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_206)))) | ~v1_funct_2(E_209, u1_struct_0('#skF_3'), u1_struct_0(B_206)) | ~v1_funct_1(E_209) | ~l1_pre_topc(B_206) | ~v2_pre_topc(B_206) | v2_struct_0(B_206))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_569])).
% 13.59/5.50  tff(c_397, plain, (![B_200, C_198, F_201, E_203, D_202, A_199]: (v1_funct_2(k10_tmap_1(A_199, B_200, C_198, D_202, E_203, F_201), u1_struct_0(k1_tsep_1(A_199, C_198, D_202)), u1_struct_0(B_200)) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_202), u1_struct_0(B_200)))) | ~v1_funct_2(F_201, u1_struct_0(D_202), u1_struct_0(B_200)) | ~v1_funct_1(F_201) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_198), u1_struct_0(B_200)))) | ~v1_funct_2(E_203, u1_struct_0(C_198), u1_struct_0(B_200)) | ~v1_funct_1(E_203) | ~m1_pre_topc(D_202, A_199) | v2_struct_0(D_202) | ~m1_pre_topc(C_198, A_199) | v2_struct_0(C_198) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.59/5.50  tff(c_400, plain, (![B_200, E_203, F_201]: (v1_funct_2(k10_tmap_1('#skF_1', B_200, '#skF_3', '#skF_4', E_203, F_201), u1_struct_0('#skF_1'), u1_struct_0(B_200)) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_200)))) | ~v1_funct_2(F_201, u1_struct_0('#skF_4'), u1_struct_0(B_200)) | ~v1_funct_1(F_201) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200)))) | ~v1_funct_2(E_203, u1_struct_0('#skF_3'), u1_struct_0(B_200)) | ~v1_funct_1(E_203) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_397])).
% 13.59/5.50  tff(c_402, plain, (![B_200, E_203, F_201]: (v1_funct_2(k10_tmap_1('#skF_1', B_200, '#skF_3', '#skF_4', E_203, F_201), u1_struct_0('#skF_1'), u1_struct_0(B_200)) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_200)))) | ~v1_funct_2(F_201, u1_struct_0('#skF_4'), u1_struct_0(B_200)) | ~v1_funct_1(F_201) | ~m1_subset_1(E_203, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200)))) | ~v1_funct_2(E_203, u1_struct_0('#skF_3'), u1_struct_0(B_200)) | ~v1_funct_1(E_203) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_400])).
% 13.59/5.50  tff(c_1189, plain, (![B_263, E_264, F_265]: (v1_funct_2(k10_tmap_1('#skF_1', B_263, '#skF_3', '#skF_4', E_264, F_265), u1_struct_0('#skF_1'), u1_struct_0(B_263)) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_263)))) | ~v1_funct_2(F_265, u1_struct_0('#skF_4'), u1_struct_0(B_263)) | ~v1_funct_1(F_265) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_263)))) | ~v1_funct_2(E_264, u1_struct_0('#skF_3'), u1_struct_0(B_263)) | ~v1_funct_1(E_264) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_402])).
% 13.59/5.50  tff(c_1200, plain, (![E_264]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_264, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_264, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_264) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_493, c_1189])).
% 13.59/5.50  tff(c_1218, plain, (![E_264]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_264, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_264, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_264) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_499, c_496, c_1200])).
% 13.59/5.50  tff(c_1219, plain, (![E_264]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_264, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_264, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_264))), inference(negUnitSimplification, [status(thm)], [c_56, c_1218])).
% 13.59/5.50  tff(c_20, plain, (![F_64, D_62, A_59, C_61, E_63, B_60]: (v1_funct_1(k10_tmap_1(A_59, B_60, C_61, D_62, E_63, F_64)) | ~m1_subset_1(F_64, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_62), u1_struct_0(B_60)))) | ~v1_funct_2(F_64, u1_struct_0(D_62), u1_struct_0(B_60)) | ~v1_funct_1(F_64) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0(B_60)))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0(B_60)) | ~v1_funct_1(E_63) | ~m1_pre_topc(D_62, A_59) | v2_struct_0(D_62) | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc(B_60) | ~v2_pre_topc(B_60) | v2_struct_0(B_60) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.59/5.50  tff(c_503, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(resolution, [status(thm)], [c_493, c_20])).
% 13.59/5.50  tff(c_518, plain, (![A_59, C_61, E_63]: (v1_funct_1(k10_tmap_1(A_59, '#skF_2', C_61, '#skF_4', E_63, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_63, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_61), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_63, u1_struct_0(C_61), u1_struct_0('#skF_2')) | ~v1_funct_1(E_63) | ~m1_pre_topc('#skF_4', A_59) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_61, A_59) | v2_struct_0(C_61) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_499, c_496, c_503])).
% 13.59/5.50  tff(c_2347, plain, (![A_301, C_302, E_303]: (v1_funct_1(k10_tmap_1(A_301, '#skF_2', C_302, '#skF_4', E_303, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_subset_1(E_303, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_302), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_303, u1_struct_0(C_302), u1_struct_0('#skF_2')) | ~v1_funct_1(E_303) | ~m1_pre_topc('#skF_4', A_301) | ~m1_pre_topc(C_302, A_301) | v2_struct_0(C_302) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(negUnitSimplification, [status(thm)], [c_56, c_46, c_518])).
% 13.59/5.50  tff(c_2391, plain, (![A_301]: (v1_funct_1(k10_tmap_1(A_301, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~m1_pre_topc('#skF_4', A_301) | ~m1_pre_topc('#skF_3', A_301) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(resolution, [status(thm)], [c_284, c_2347])).
% 13.59/5.50  tff(c_2449, plain, (![A_301]: (v1_funct_1(k10_tmap_1(A_301, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_301) | ~m1_pre_topc('#skF_3', A_301) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_287, c_2391])).
% 13.59/5.50  tff(c_2450, plain, (![A_301]: (v1_funct_1(k10_tmap_1(A_301, '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_4', A_301) | ~m1_pre_topc('#skF_3', A_301) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301) | v2_struct_0(A_301))), inference(negUnitSimplification, [status(thm)], [c_50, c_2449])).
% 13.59/5.50  tff(c_1387, plain, (![B_272, E_273, F_274]: (m1_subset_1(k10_tmap_1('#skF_1', B_272, '#skF_3', '#skF_4', E_273, F_274), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_272)))) | ~m1_subset_1(F_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_272)))) | ~v1_funct_2(F_274, u1_struct_0('#skF_4'), u1_struct_0(B_272)) | ~v1_funct_1(F_274) | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_272)))) | ~v1_funct_2(E_273, u1_struct_0('#skF_3'), u1_struct_0(B_272)) | ~v1_funct_1(E_273) | ~l1_pre_topc(B_272) | ~v2_pre_topc(B_272) | v2_struct_0(B_272))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_569])).
% 13.59/5.50  tff(c_292, plain, (![E_197, B_194, D_196, F_195, A_193, C_192]: (v1_funct_1(k10_tmap_1(A_193, B_194, C_192, D_196, E_197, F_195)) | ~m1_subset_1(F_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_196), u1_struct_0(B_194)))) | ~v1_funct_2(F_195, u1_struct_0(D_196), u1_struct_0(B_194)) | ~v1_funct_1(F_195) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0(B_194)))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0(B_194)) | ~v1_funct_1(E_197) | ~m1_pre_topc(D_196, A_193) | v2_struct_0(D_196) | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | ~l1_pre_topc(B_194) | ~v2_pre_topc(B_194) | v2_struct_0(B_194) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_174])).
% 13.59/5.50  tff(c_296, plain, (![A_193, C_192, E_197]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', C_192, '#skF_1', E_197, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0('#skF_2')) | ~v1_funct_1(E_197) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(resolution, [status(thm)], [c_36, c_292])).
% 13.59/5.50  tff(c_300, plain, (![A_193, C_192, E_197]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', C_192, '#skF_1', E_197, '#skF_5')) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0('#skF_2')) | ~v1_funct_1(E_197) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_296])).
% 13.59/5.50  tff(c_301, plain, (![A_193, C_192, E_197]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', C_192, '#skF_1', E_197, '#skF_5')) | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_192), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_197, u1_struct_0(C_192), u1_struct_0('#skF_2')) | ~v1_funct_1(E_197) | ~m1_pre_topc('#skF_1', A_193) | ~m1_pre_topc(C_192, A_193) | v2_struct_0(C_192) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_300])).
% 13.59/5.50  tff(c_1390, plain, (![A_193, E_273, F_274]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_273, F_274), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_273, F_274), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_273, F_274)) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193) | ~m1_subset_1(F_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_274, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_274) | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_273, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_273) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1387, c_301])).
% 13.59/5.50  tff(c_1407, plain, (![A_193, E_273, F_274]: (v1_funct_1(k10_tmap_1(A_193, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_273, F_274), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_273, F_274), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_273, F_274)) | ~m1_pre_topc('#skF_1', A_193) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | v2_struct_0(A_193) | ~m1_subset_1(F_274, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_274, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_274) | ~m1_subset_1(E_273, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_273, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_273) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1390])).
% 13.59/5.50  tff(c_7290, plain, (![A_753, E_754, F_755]: (v1_funct_1(k10_tmap_1(A_753, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_754, F_755), '#skF_5')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_754, F_755), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_754, F_755)) | ~m1_pre_topc('#skF_1', A_753) | ~l1_pre_topc(A_753) | ~v2_pre_topc(A_753) | v2_struct_0(A_753) | ~m1_subset_1(F_755, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(F_755, u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(F_755) | ~m1_subset_1(E_754, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_754, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_754))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_1407])).
% 13.59/5.50  tff(c_7292, plain, (![A_753, E_264]: (v1_funct_1(k10_tmap_1(A_753, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_264, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_264, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_753) | ~l1_pre_topc(A_753) | ~v2_pre_topc(A_753) | v2_struct_0(A_753) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_264, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_264))), inference(resolution, [status(thm)], [c_1219, c_7290])).
% 13.59/5.50  tff(c_7986, plain, (![A_788, E_789]: (v1_funct_1(k10_tmap_1(A_788, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_789, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_789, k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_788) | ~l1_pre_topc(A_788) | ~v2_pre_topc(A_788) | v2_struct_0(A_788) | ~m1_subset_1(E_789, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_789, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_789))), inference(demodulation, [status(thm), theory('equality')], [c_499, c_496, c_493, c_7292])).
% 13.59/5.50  tff(c_8024, plain, (![A_788]: (v1_funct_1(k10_tmap_1(A_788, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_788) | ~l1_pre_topc(A_788) | ~v2_pre_topc(A_788) | v2_struct_0(A_788) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')))), inference(resolution, [status(thm)], [c_284, c_7986])).
% 13.59/5.50  tff(c_8069, plain, (![A_788]: (v1_funct_1(k10_tmap_1(A_788, '#skF_2', '#skF_1', '#skF_1', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), '#skF_5')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))) | ~m1_pre_topc('#skF_1', A_788) | ~l1_pre_topc(A_788) | ~v2_pre_topc(A_788) | v2_struct_0(A_788))), inference(demodulation, [status(thm), theory('equality')], [c_290, c_287, c_8024])).
% 13.59/5.50  tff(c_8074, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitLeft, [status(thm)], [c_8069])).
% 13.59/5.50  tff(c_8077, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2450, c_8074])).
% 13.59/5.50  tff(c_8080, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_8077])).
% 13.59/5.50  tff(c_8082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_8080])).
% 13.59/5.50  tff(c_8084, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(splitRight, [status(thm)], [c_8069])).
% 13.59/5.50  tff(c_626, plain, (![B_221, D_225, E_224, C_223, A_222]: (r2_funct_2(u1_struct_0(k1_tsep_1(A_222, C_223, D_225)), u1_struct_0(B_221), E_224, k10_tmap_1(A_222, B_221, C_223, D_225, k3_tmap_1(A_222, B_221, k1_tsep_1(A_222, C_223, D_225), C_223, E_224), k3_tmap_1(A_222, B_221, k1_tsep_1(A_222, C_223, D_225), D_225, E_224))) | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_222, C_223, D_225)), u1_struct_0(B_221)))) | ~v1_funct_2(E_224, u1_struct_0(k1_tsep_1(A_222, C_223, D_225)), u1_struct_0(B_221)) | ~v1_funct_1(E_224) | ~m1_pre_topc(D_225, A_222) | v2_struct_0(D_225) | ~m1_pre_topc(C_223, A_222) | v2_struct_0(C_223) | ~l1_pre_topc(B_221) | ~v2_pre_topc(B_221) | v2_struct_0(B_221) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_240])).
% 13.59/5.50  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.59/5.50  tff(c_6086, plain, (![E_659, C_658, B_661, D_660, A_662]: (k10_tmap_1(A_662, B_661, C_658, D_660, k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), C_658, E_659), k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), D_660, E_659))=E_659 | ~m1_subset_1(k10_tmap_1(A_662, B_661, C_658, D_660, k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), C_658, E_659), k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), D_660, E_659)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_662, C_658, D_660)), u1_struct_0(B_661)))) | ~v1_funct_2(k10_tmap_1(A_662, B_661, C_658, D_660, k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), C_658, E_659), k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), D_660, E_659)), u1_struct_0(k1_tsep_1(A_662, C_658, D_660)), u1_struct_0(B_661)) | ~v1_funct_1(k10_tmap_1(A_662, B_661, C_658, D_660, k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), C_658, E_659), k3_tmap_1(A_662, B_661, k1_tsep_1(A_662, C_658, D_660), D_660, E_659))) | ~m1_subset_1(E_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_662, C_658, D_660)), u1_struct_0(B_661)))) | ~v1_funct_2(E_659, u1_struct_0(k1_tsep_1(A_662, C_658, D_660)), u1_struct_0(B_661)) | ~v1_funct_1(E_659) | ~m1_pre_topc(D_660, A_662) | v2_struct_0(D_660) | ~m1_pre_topc(C_658, A_662) | v2_struct_0(C_658) | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | v2_struct_0(B_661) | ~l1_pre_topc(A_662) | ~v2_pre_topc(A_662) | v2_struct_0(A_662))), inference(resolution, [status(thm)], [c_626, c_4])).
% 13.59/5.50  tff(c_6101, plain, (![B_661, E_659]: (k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_659))=E_659 | ~m1_subset_1(k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_659)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_661)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_659)), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_661)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_659))) | ~m1_subset_1(E_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_661)))) | ~v1_funct_2(E_659, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_661)) | ~v1_funct_1(E_659) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | v2_struct_0(B_661) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_6086])).
% 13.59/5.50  tff(c_6110, plain, (![B_661, E_659]: (k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_4', E_659))=E_659 | ~m1_subset_1(k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_4', E_659)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_661)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_4', E_659)), u1_struct_0('#skF_1'), u1_struct_0(B_661)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_661, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_3', E_659), k3_tmap_1('#skF_1', B_661, '#skF_1', '#skF_4', E_659))) | ~m1_subset_1(E_659, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_661)))) | ~v1_funct_2(E_659, u1_struct_0('#skF_1'), u1_struct_0(B_661)) | ~v1_funct_1(E_659) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_661) | ~v2_pre_topc(B_661) | v2_struct_0(B_661) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48, c_44, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_42, c_6101])).
% 13.59/5.50  tff(c_11432, plain, (![B_998, E_999]: (k10_tmap_1('#skF_1', B_998, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_3', E_999), k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_4', E_999))=E_999 | ~m1_subset_1(k10_tmap_1('#skF_1', B_998, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_3', E_999), k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_4', E_999)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_998)))) | ~v1_funct_2(k10_tmap_1('#skF_1', B_998, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_3', E_999), k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_4', E_999)), u1_struct_0('#skF_1'), u1_struct_0(B_998)) | ~v1_funct_1(k10_tmap_1('#skF_1', B_998, '#skF_3', '#skF_4', k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_3', E_999), k3_tmap_1('#skF_1', B_998, '#skF_1', '#skF_4', E_999))) | ~m1_subset_1(E_999, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_998)))) | ~v1_funct_2(E_999, u1_struct_0('#skF_1'), u1_struct_0(B_998)) | ~v1_funct_1(E_999) | ~l1_pre_topc(B_998) | ~v2_pre_topc(B_998) | v2_struct_0(B_998))), inference(negUnitSimplification, [status(thm)], [c_62, c_50, c_46, c_6110])).
% 13.59/5.50  tff(c_11471, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_474, c_11432])).
% 13.59/5.50  tff(c_11501, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_40, c_38, c_36, c_8084, c_265, c_474, c_265, c_474, c_265, c_265, c_474, c_11471])).
% 13.59/5.50  tff(c_11502, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5' | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_11501])).
% 13.59/5.50  tff(c_11522, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_11502])).
% 13.59/5.50  tff(c_11525, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_1219, c_11522])).
% 13.59/5.50  tff(c_11529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_290, c_287, c_284, c_11525])).
% 13.59/5.50  tff(c_11530, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_11502])).
% 13.59/5.50  tff(c_11584, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_11530])).
% 13.59/5.50  tff(c_11587, plain, (~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')) | ~m1_subset_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_570, c_11584])).
% 13.59/5.50  tff(c_11590, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_290, c_287, c_284, c_499, c_496, c_493, c_11587])).
% 13.59/5.50  tff(c_11592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_11590])).
% 13.59/5.50  tff(c_11593, plain, (k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_11530])).
% 13.59/5.50  tff(c_34, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_295])).
% 13.59/5.50  tff(c_63, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_3'), k2_tmap_1('#skF_1', '#skF_2', '#skF_5', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34])).
% 13.59/5.50  tff(c_11600, plain, (~r1_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11593, c_63])).
% 13.59/5.50  tff(c_11728, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4508, c_11600])).
% 13.59/5.50  tff(c_11740, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_44, c_40, c_38, c_36, c_11728])).
% 13.59/5.50  tff(c_11742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_144, c_11740])).
% 13.59/5.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.59/5.50  
% 13.59/5.50  Inference rules
% 13.59/5.50  ----------------------
% 13.59/5.50  #Ref     : 0
% 13.59/5.50  #Sup     : 2185
% 13.59/5.50  #Fact    : 0
% 13.59/5.50  #Define  : 0
% 13.59/5.50  #Split   : 26
% 13.59/5.50  #Chain   : 0
% 13.59/5.50  #Close   : 0
% 13.59/5.50  
% 13.59/5.50  Ordering : KBO
% 13.59/5.50  
% 13.59/5.50  Simplification rules
% 13.59/5.50  ----------------------
% 13.59/5.50  #Subsume      : 1101
% 13.59/5.50  #Demod        : 6477
% 13.59/5.50  #Tautology    : 362
% 13.59/5.50  #SimpNegUnit  : 1173
% 13.59/5.50  #BackRed      : 45
% 13.59/5.50  
% 13.59/5.50  #Partial instantiations: 0
% 13.59/5.50  #Strategies tried      : 1
% 13.59/5.50  
% 13.59/5.50  Timing (in seconds)
% 13.59/5.50  ----------------------
% 13.59/5.50  Preprocessing        : 0.41
% 13.59/5.50  Parsing              : 0.22
% 13.59/5.50  CNF conversion       : 0.05
% 13.59/5.50  Main loop            : 4.30
% 13.59/5.50  Inferencing          : 1.27
% 13.59/5.50  Reduction            : 1.59
% 13.59/5.50  Demodulation         : 1.25
% 13.59/5.50  BG Simplification    : 0.08
% 13.59/5.50  Subsumption          : 1.21
% 13.59/5.50  Abstraction          : 0.17
% 13.59/5.50  MUC search           : 0.00
% 13.59/5.50  Cooper               : 0.00
% 13.59/5.50  Total                : 4.77
% 13.59/5.50  Index Insertion      : 0.00
% 13.59/5.50  Index Deletion       : 0.00
% 13.59/5.50  Index Matching       : 0.00
% 13.59/5.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
