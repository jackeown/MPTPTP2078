%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:46 EST 2020

% Result     : Theorem 9.64s
% Output     : CNFRefutation 9.85s
% Verified   : 
% Statistics : Number of formulae       :  192 (12705 expanded)
%              Number of leaves         :   44 (5001 expanded)
%              Depth                    :   39
%              Number of atoms          :  815 (86762 expanded)
%              Number of equality atoms :   64 (6164 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tmap_1,type,(
    k4_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_348,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
               => ( ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_hidden(D,u1_struct_0(B))
                       => D = k1_funct_1(C,D) ) )
                 => r2_funct_2(u1_struct_0(B),u1_struct_0(A),k4_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_208,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_60,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_212,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_286,axiom,(
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
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(C),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                 => r2_funct_2(u1_struct_0(C),u1_struct_0(B),D,k3_tmap_1(A,B,C,C,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

tff(f_163,axiom,(
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

tff(f_131,axiom,(
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

tff(f_256,axiom,(
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
                & m1_pre_topc(C,B) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,u1_struct_0(B))
                           => ( r2_hidden(F,u1_struct_0(C))
                             => k3_funct_2(u1_struct_0(B),u1_struct_0(A),D,F) = k1_funct_1(E,F) ) )
                       => r2_funct_2(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_104,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_318,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,u1_struct_0(B))
               => k1_funct_1(k4_tmap_1(A,B),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_tmap_1)).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_71,plain,(
    ! [B_185,A_186] :
      ( l1_pre_topc(B_185)
      | ~ m1_pre_topc(B_185,A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_71])).

tff(c_81,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_77])).

tff(c_12,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [D_192] :
      ( k1_funct_1('#skF_4',D_192) = D_192
      | ~ r2_hidden(D_192,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_192,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_100,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_102,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_16,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_105,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_16])).

tff(c_108,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_105])).

tff(c_111,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_108])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_111])).

tff(c_117,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_30,plain,(
    ! [A_77,B_78] :
      ( m1_subset_1(k4_tmap_1(A_77,B_78),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_78),u1_struct_0(A_77))))
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_56,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_135,plain,(
    ! [A_202,B_203,D_204] :
      ( r2_funct_2(A_202,B_203,D_204,D_204)
      | ~ m1_subset_1(D_204,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203)))
      | ~ v1_funct_2(D_204,A_202,B_203)
      | ~ v1_funct_1(D_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_135])).

tff(c_140,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_137])).

tff(c_34,plain,(
    ! [A_77,B_78] :
      ( v1_funct_1(k4_tmap_1(A_77,B_78))
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_84,plain,(
    ! [B_190,A_191] :
      ( v2_pre_topc(B_190)
      | ~ m1_pre_topc(B_190,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_90,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_94,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_90])).

tff(c_36,plain,(
    ! [A_79] :
      ( m1_pre_topc(A_79,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_166,plain,(
    ! [E_227,D_228,C_226,A_225,B_224] :
      ( v1_funct_1(k3_tmap_1(A_225,B_224,C_226,D_228,E_227))
      | ~ m1_subset_1(E_227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_226),u1_struct_0(B_224))))
      | ~ v1_funct_2(E_227,u1_struct_0(C_226),u1_struct_0(B_224))
      | ~ v1_funct_1(E_227)
      | ~ m1_pre_topc(D_228,A_225)
      | ~ m1_pre_topc(C_226,A_225)
      | ~ l1_pre_topc(B_224)
      | ~ v2_pre_topc(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_170,plain,(
    ! [A_225,D_228] :
      ( v1_funct_1(k3_tmap_1(A_225,'#skF_2','#skF_3',D_228,'#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_228,A_225)
      | ~ m1_pre_topc('#skF_3',A_225)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(resolution,[status(thm)],[c_54,c_166])).

tff(c_174,plain,(
    ! [A_225,D_228] :
      ( v1_funct_1(k3_tmap_1(A_225,'#skF_2','#skF_3',D_228,'#skF_4'))
      | ~ m1_pre_topc(D_228,A_225)
      | ~ m1_pre_topc('#skF_3',A_225)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_170])).

tff(c_175,plain,(
    ! [A_225,D_228] :
      ( v1_funct_1(k3_tmap_1(A_225,'#skF_2','#skF_3',D_228,'#skF_4'))
      | ~ m1_pre_topc(D_228,A_225)
      | ~ m1_pre_topc('#skF_3',A_225)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_174])).

tff(c_217,plain,(
    ! [B_250,C_252,D_254,E_253,A_251] :
      ( v1_funct_2(k3_tmap_1(A_251,B_250,C_252,D_254,E_253),u1_struct_0(D_254),u1_struct_0(B_250))
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252),u1_struct_0(B_250))))
      | ~ v1_funct_2(E_253,u1_struct_0(C_252),u1_struct_0(B_250))
      | ~ v1_funct_1(E_253)
      | ~ m1_pre_topc(D_254,A_251)
      | ~ m1_pre_topc(C_252,A_251)
      | ~ l1_pre_topc(B_250)
      | ~ v2_pre_topc(B_250)
      | v2_struct_0(B_250)
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_221,plain,(
    ! [A_251,D_254] :
      ( v1_funct_2(k3_tmap_1(A_251,'#skF_2','#skF_3',D_254,'#skF_4'),u1_struct_0(D_254),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_254,A_251)
      | ~ m1_pre_topc('#skF_3',A_251)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_54,c_217])).

tff(c_225,plain,(
    ! [A_251,D_254] :
      ( v1_funct_2(k3_tmap_1(A_251,'#skF_2','#skF_3',D_254,'#skF_4'),u1_struct_0(D_254),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_254,A_251)
      | ~ m1_pre_topc('#skF_3',A_251)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_221])).

tff(c_226,plain,(
    ! [A_251,D_254] :
      ( v1_funct_2(k3_tmap_1(A_251,'#skF_2','#skF_3',D_254,'#skF_4'),u1_struct_0(D_254),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_254,A_251)
      | ~ m1_pre_topc('#skF_3',A_251)
      | ~ l1_pre_topc(A_251)
      | ~ v2_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_225])).

tff(c_236,plain,(
    ! [E_266,D_267,A_264,C_265,B_263] :
      ( m1_subset_1(k3_tmap_1(A_264,B_263,C_265,D_267,E_266),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_267),u1_struct_0(B_263))))
      | ~ m1_subset_1(E_266,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_265),u1_struct_0(B_263))))
      | ~ v1_funct_2(E_266,u1_struct_0(C_265),u1_struct_0(B_263))
      | ~ v1_funct_1(E_266)
      | ~ m1_pre_topc(D_267,A_264)
      | ~ m1_pre_topc(C_265,A_264)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_207,plain,(
    ! [C_246,B_247,D_248,A_249] :
      ( r2_funct_2(u1_struct_0(C_246),u1_struct_0(B_247),D_248,k3_tmap_1(A_249,B_247,C_246,C_246,D_248))
      | ~ m1_subset_1(D_248,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_246),u1_struct_0(B_247))))
      | ~ v1_funct_2(D_248,u1_struct_0(C_246),u1_struct_0(B_247))
      | ~ v1_funct_1(D_248)
      | ~ m1_pre_topc(C_246,A_249)
      | v2_struct_0(C_246)
      | ~ l1_pre_topc(B_247)
      | ~ v2_pre_topc(B_247)
      | v2_struct_0(B_247)
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_211,plain,(
    ! [A_249] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_249,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_249)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(resolution,[status(thm)],[c_54,c_207])).

tff(c_215,plain,(
    ! [A_249] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_249,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_249)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249)
      | v2_struct_0(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_211])).

tff(c_227,plain,(
    ! [A_255] :
      ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_215])).

tff(c_8,plain,(
    ! [D_10,C_9,A_7,B_8] :
      ( D_10 = C_9
      | ~ r2_funct_2(A_7,B_8,C_9,D_10)
      | ~ m1_subset_1(D_10,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(D_10,A_7,B_8)
      | ~ v1_funct_1(D_10)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_2(C_9,A_7,B_8)
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_229,plain,(
    ! [A_255] :
      ( k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_227,c_8])).

tff(c_232,plain,(
    ! [A_255] :
      ( k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_subset_1(k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_255,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_229])).

tff(c_240,plain,(
    ! [A_264] :
      ( k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_264)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_236,c_232])).

tff(c_255,plain,(
    ! [A_264] :
      ( k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_264,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_264)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_240])).

tff(c_263,plain,(
    ! [A_268] :
      ( k3_tmap_1(A_268,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_2(k3_tmap_1(A_268,'#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1(A_268,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_268)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_255])).

tff(c_269,plain,(
    ! [A_269] :
      ( k3_tmap_1(A_269,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ v1_funct_1(k3_tmap_1(A_269,'#skF_2','#skF_3','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_269)
      | ~ l1_pre_topc(A_269)
      | ~ v2_pre_topc(A_269)
      | v2_struct_0(A_269) ) ),
    inference(resolution,[status(thm)],[c_226,c_263])).

tff(c_275,plain,(
    ! [A_270] :
      ( k3_tmap_1(A_270,'#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
      | ~ m1_pre_topc('#skF_3',A_270)
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_175,c_269])).

tff(c_282,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_275])).

tff(c_289,plain,
    ( k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_282])).

tff(c_290,plain,(
    k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_289])).

tff(c_319,plain,(
    ! [A_271,C_274,D_275,E_272,B_273] :
      ( k3_tmap_1(A_271,B_273,C_274,D_275,E_272) = k2_partfun1(u1_struct_0(C_274),u1_struct_0(B_273),E_272,u1_struct_0(D_275))
      | ~ m1_pre_topc(D_275,C_274)
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274),u1_struct_0(B_273))))
      | ~ v1_funct_2(E_272,u1_struct_0(C_274),u1_struct_0(B_273))
      | ~ v1_funct_1(E_272)
      | ~ m1_pre_topc(D_275,A_271)
      | ~ m1_pre_topc(C_274,A_271)
      | ~ l1_pre_topc(B_273)
      | ~ v2_pre_topc(B_273)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_325,plain,(
    ! [A_271,D_275] :
      ( k3_tmap_1(A_271,'#skF_2','#skF_3',D_275,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_275))
      | ~ m1_pre_topc(D_275,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(D_275,A_271)
      | ~ m1_pre_topc('#skF_3',A_271)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(resolution,[status(thm)],[c_54,c_319])).

tff(c_330,plain,(
    ! [A_271,D_275] :
      ( k3_tmap_1(A_271,'#skF_2','#skF_3',D_275,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_275))
      | ~ m1_pre_topc(D_275,'#skF_3')
      | ~ m1_pre_topc(D_275,A_271)
      | ~ m1_pre_topc('#skF_3',A_271)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_271)
      | ~ v2_pre_topc(A_271)
      | v2_struct_0(A_271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_325])).

tff(c_360,plain,(
    ! [A_276,D_277] :
      ( k3_tmap_1(A_276,'#skF_2','#skF_3',D_277,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_277))
      | ~ m1_pre_topc(D_277,'#skF_3')
      | ~ m1_pre_topc(D_277,A_276)
      | ~ m1_pre_topc('#skF_3',A_276)
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_330])).

tff(c_364,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_2','#skF_3','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_360])).

tff(c_368,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_290,c_364])).

tff(c_369,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_368])).

tff(c_370,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_373,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_370])).

tff(c_377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_373])).

tff(c_379,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_378,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_188,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k2_partfun1(u1_struct_0(A_241),u1_struct_0(B_242),C_243,u1_struct_0(D_244)) = k2_tmap_1(A_241,B_242,C_243,D_244)
      | ~ m1_pre_topc(D_244,A_241)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241),u1_struct_0(B_242))))
      | ~ v1_funct_2(C_243,u1_struct_0(A_241),u1_struct_0(B_242))
      | ~ v1_funct_1(C_243)
      | ~ l1_pre_topc(B_242)
      | ~ v2_pre_topc(B_242)
      | v2_struct_0(B_242)
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_192,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_244)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_244)
      | ~ m1_pre_topc(D_244,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_188])).

tff(c_196,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_244)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_244)
      | ~ m1_pre_topc(D_244,'#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_81,c_66,c_64,c_58,c_56,c_192])).

tff(c_197,plain,(
    ! [D_244] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(D_244)) = k2_tmap_1('#skF_3','#skF_2','#skF_4',D_244)
      | ~ m1_pre_topc(D_244,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_196])).

tff(c_411,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_197])).

tff(c_418,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_411])).

tff(c_646,plain,(
    ! [A_291,C_292,D_293,B_294,E_295] :
      ( m1_subset_1('#skF_1'(A_291,C_292,D_293,B_294,E_295),u1_struct_0(B_294))
      | r2_funct_2(u1_struct_0(C_292),u1_struct_0(A_291),k2_tmap_1(B_294,A_291,D_293,C_292),E_295)
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292),u1_struct_0(A_291))))
      | ~ v1_funct_2(E_295,u1_struct_0(C_292),u1_struct_0(A_291))
      | ~ v1_funct_1(E_295)
      | ~ m1_subset_1(D_293,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_294),u1_struct_0(A_291))))
      | ~ v1_funct_2(D_293,u1_struct_0(B_294),u1_struct_0(A_291))
      | ~ v1_funct_1(D_293)
      | ~ m1_pre_topc(C_292,B_294)
      | v2_struct_0(C_292)
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_1212,plain,(
    ! [A_357,B_358,D_359,B_360] :
      ( m1_subset_1('#skF_1'(A_357,B_358,D_359,B_360,k4_tmap_1(A_357,B_358)),u1_struct_0(B_360))
      | r2_funct_2(u1_struct_0(B_358),u1_struct_0(A_357),k2_tmap_1(B_360,A_357,D_359,B_358),k4_tmap_1(A_357,B_358))
      | ~ v1_funct_2(k4_tmap_1(A_357,B_358),u1_struct_0(B_358),u1_struct_0(A_357))
      | ~ v1_funct_1(k4_tmap_1(A_357,B_358))
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_360),u1_struct_0(A_357))))
      | ~ v1_funct_2(D_359,u1_struct_0(B_360),u1_struct_0(A_357))
      | ~ v1_funct_1(D_359)
      | ~ m1_pre_topc(B_358,B_360)
      | v2_struct_0(B_358)
      | ~ l1_pre_topc(B_360)
      | ~ v2_pre_topc(B_360)
      | v2_struct_0(B_360)
      | ~ m1_pre_topc(B_358,A_357)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | v2_struct_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_30,c_646])).

tff(c_1225,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_1212])).

tff(c_1231,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_94,c_81,c_379,c_58,c_56,c_54,c_1225])).

tff(c_1232,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1231])).

tff(c_1233,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_1236,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_1233])).

tff(c_1239,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1236])).

tff(c_1241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1239])).

tff(c_1243,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_32,plain,(
    ! [A_77,B_78] :
      ( v1_funct_2(k4_tmap_1(A_77,B_78),u1_struct_0(B_78),u1_struct_0(A_77))
      | ~ m1_pre_topc(B_78,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1242,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_1262,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1242])).

tff(c_1265,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1262])).

tff(c_1268,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1265])).

tff(c_1270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1268])).

tff(c_1272,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_1271,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1242])).

tff(c_1273,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1271])).

tff(c_1275,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1273,c_8])).

tff(c_1278,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1243,c_1272,c_1275])).

tff(c_1289,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1278])).

tff(c_1292,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1289])).

tff(c_1295,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1292])).

tff(c_1297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1295])).

tff(c_1298,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1278])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_348])).

tff(c_1303,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_50])).

tff(c_1309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1303])).

tff(c_1311,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1271])).

tff(c_279,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_275])).

tff(c_285,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_94,c_279])).

tff(c_286,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_285])).

tff(c_1310,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1271])).

tff(c_18,plain,(
    ! [C_25,A_19,B_23] :
      ( m1_subset_1(C_25,u1_struct_0(A_19))
      | ~ m1_subset_1(C_25,u1_struct_0(B_23))
      | ~ m1_pre_topc(B_23,A_19)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1333,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(A_19))
      | ~ m1_pre_topc('#skF_3',A_19)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_1310,c_18])).

tff(c_1344,plain,(
    ! [A_369] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(A_369))
      | ~ m1_pre_topc('#skF_3',A_369)
      | ~ l1_pre_topc(A_369)
      | v2_struct_0(A_369) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1333])).

tff(c_116,plain,(
    ! [A_1] :
      ( k1_funct_1('#skF_4',A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(A_1,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_1354,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1344,c_116])).

tff(c_1360,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1310,c_1354])).

tff(c_1361,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1360])).

tff(c_365,plain,(
    ! [A_79] :
      ( k3_tmap_1(A_79,'#skF_2','#skF_3',A_79,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_79))
      | ~ m1_pre_topc(A_79,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_36,c_360])).

tff(c_441,plain,(
    ! [A_283] :
      ( k3_tmap_1(A_283,'#skF_2','#skF_3',A_283,'#skF_4') = k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_283))
      | ~ m1_pre_topc(A_283,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283)
      | ~ l1_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_36,c_360])).

tff(c_24,plain,(
    ! [B_73,C_74,E_76,A_72,D_75] :
      ( m1_subset_1(k3_tmap_1(A_72,B_73,C_74,D_75,E_76),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_75),u1_struct_0(B_73))))
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_74),u1_struct_0(B_73))))
      | ~ v1_funct_2(E_76,u1_struct_0(C_74),u1_struct_0(B_73))
      | ~ v1_funct_1(E_76)
      | ~ m1_pre_topc(D_75,A_72)
      | ~ m1_pre_topc(C_74,A_72)
      | ~ l1_pre_topc(B_73)
      | ~ v2_pre_topc(B_73)
      | v2_struct_0(B_73)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_453,plain,(
    ! [A_283] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_283)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283),u1_struct_0('#skF_2'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_pre_topc(A_283,A_283)
      | ~ m1_pre_topc('#skF_3',A_283)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283)
      | ~ m1_pre_topc(A_283,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283)
      | ~ l1_pre_topc(A_283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_24])).

tff(c_481,plain,(
    ! [A_283] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_283)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_283,A_283)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(A_283,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283)
      | ~ l1_pre_topc(A_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_453])).

tff(c_502,plain,(
    ! [A_285] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',u1_struct_0(A_285)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_285,A_285)
      | ~ m1_pre_topc(A_285,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285)
      | ~ l1_pre_topc(A_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_481])).

tff(c_521,plain,(
    ! [A_79] :
      ( m1_subset_1(k3_tmap_1(A_79,'#skF_2','#skF_3',A_79,'#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_79),u1_struct_0('#skF_2'))))
      | ~ m1_pre_topc(A_79,A_79)
      | ~ m1_pre_topc(A_79,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79)
      | ~ l1_pre_topc(A_79)
      | ~ m1_pre_topc(A_79,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_502])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5,D_6] :
      ( k3_funct_2(A_3,B_4,C_5,D_6) = k1_funct_1(C_5,D_6)
      | ~ m1_subset_1(D_6,A_3)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ v1_funct_2(C_5,A_3,B_4)
      | ~ v1_funct_1(C_5)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1331,plain,(
    ! [B_4,C_5] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_4,C_5,'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = k1_funct_1(C_5,'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_4)))
      | ~ v1_funct_2(C_5,u1_struct_0('#skF_3'),B_4)
      | ~ v1_funct_1(C_5)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1310,c_4])).

tff(c_1570,plain,(
    ! [B_389,C_390] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_389,C_390,'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = k1_funct_1(C_390,'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(C_390,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_389)))
      | ~ v1_funct_2(C_390,u1_struct_0('#skF_3'),B_389)
      | ~ v1_funct_1(C_390) ) ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_1331])).

tff(c_1574,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = k1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_3','#skF_2','#skF_3','#skF_3','#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_521,c_1570])).

tff(c_1596,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_94,c_379,c_58,c_286,c_56,c_286,c_1361,c_286,c_286,c_1574])).

tff(c_1597,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1596])).

tff(c_38,plain,(
    ! [E_140,C_128,D_136,A_80,B_112] :
      ( k3_funct_2(u1_struct_0(B_112),u1_struct_0(A_80),D_136,'#skF_1'(A_80,C_128,D_136,B_112,E_140)) != k1_funct_1(E_140,'#skF_1'(A_80,C_128,D_136,B_112,E_140))
      | r2_funct_2(u1_struct_0(C_128),u1_struct_0(A_80),k2_tmap_1(B_112,A_80,D_136,C_128),E_140)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_128),u1_struct_0(A_80))))
      | ~ v1_funct_2(E_140,u1_struct_0(C_128),u1_struct_0(A_80))
      | ~ v1_funct_1(E_140)
      | ~ m1_subset_1(D_136,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112),u1_struct_0(A_80))))
      | ~ v1_funct_2(D_136,u1_struct_0(B_112),u1_struct_0(A_80))
      | ~ v1_funct_1(D_136)
      | ~ m1_pre_topc(C_128,B_112)
      | v2_struct_0(C_128)
      | ~ l1_pre_topc(B_112)
      | ~ v2_pre_topc(B_112)
      | v2_struct_0(B_112)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_256])).

tff(c_1613,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1597,c_38])).

tff(c_1617,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_94,c_81,c_379,c_58,c_56,c_54,c_1243,c_1272,c_418,c_1613])).

tff(c_1618,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1311,c_1617])).

tff(c_1623,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1618])).

tff(c_1626,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1623])).

tff(c_1629,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1626])).

tff(c_1631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1629])).

tff(c_1632,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) != '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1618])).

tff(c_1366,plain,(
    ! [A_370,A_371] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(A_370))
      | ~ m1_pre_topc(A_371,A_370)
      | ~ l1_pre_topc(A_370)
      | v2_struct_0(A_370)
      | ~ m1_pre_topc('#skF_3',A_371)
      | ~ l1_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_1344,c_18])).

tff(c_1372,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1366])).

tff(c_1380,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_379,c_64,c_1372])).

tff(c_1381,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_1380])).

tff(c_146,plain,(
    ! [A_210,B_211,C_212] :
      ( k1_funct_1(k4_tmap_1(A_210,B_211),C_212) = C_212
      | ~ r2_hidden(C_212,u1_struct_0(B_211))
      | ~ m1_subset_1(C_212,u1_struct_0(A_210))
      | ~ m1_pre_topc(B_211,A_210)
      | v2_struct_0(B_211)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_150,plain,(
    ! [A_210,B_211,A_1] :
      ( k1_funct_1(k4_tmap_1(A_210,B_211),A_1) = A_1
      | ~ m1_subset_1(A_1,u1_struct_0(A_210))
      | ~ m1_pre_topc(B_211,A_210)
      | v2_struct_0(B_211)
      | ~ l1_pre_topc(A_210)
      | ~ v2_pre_topc(A_210)
      | v2_struct_0(A_210)
      | v1_xboole_0(u1_struct_0(B_211))
      | ~ m1_subset_1(A_1,u1_struct_0(B_211)) ) ),
    inference(resolution,[status(thm)],[c_2,c_146])).

tff(c_1403,plain,(
    ! [B_211] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_211),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_211,'#skF_2')
      | v2_struct_0(B_211)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_211))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_211)) ) ),
    inference(resolution,[status(thm)],[c_1381,c_150])).

tff(c_1413,plain,(
    ! [B_211] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_211),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_211,'#skF_2')
      | v2_struct_0(B_211)
      | v2_struct_0('#skF_2')
      | v1_xboole_0(u1_struct_0(B_211))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_211)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1403])).

tff(c_8461,plain,(
    ! [B_674] :
      ( k1_funct_1(k4_tmap_1('#skF_2',B_674),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
      | ~ m1_pre_topc(B_674,'#skF_2')
      | v2_struct_0(B_674)
      | v1_xboole_0(u1_struct_0(B_674))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3')),u1_struct_0(B_674)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1413])).

tff(c_8477,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1310,c_8461])).

tff(c_8491,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))) = '#skF_1'('#skF_2','#skF_3','#skF_4','#skF_3',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8477])).

tff(c_8493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_62,c_1632,c_8491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.64/3.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.64/3.66  
% 9.64/3.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.64/3.67  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.64/3.67  
% 9.64/3.67  %Foreground sorts:
% 9.64/3.67  
% 9.64/3.67  
% 9.64/3.67  %Background operators:
% 9.64/3.67  
% 9.64/3.67  
% 9.64/3.67  %Foreground operators:
% 9.64/3.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.64/3.67  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 9.64/3.67  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 9.64/3.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.64/3.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.64/3.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.64/3.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.64/3.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.64/3.67  tff('#skF_2', type, '#skF_2': $i).
% 9.64/3.67  tff('#skF_3', type, '#skF_3': $i).
% 9.64/3.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.64/3.67  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.64/3.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.64/3.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 9.64/3.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.64/3.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.64/3.67  tff('#skF_4', type, '#skF_4': $i).
% 9.64/3.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.64/3.67  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.64/3.67  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.64/3.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.64/3.67  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 9.64/3.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.64/3.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.64/3.67  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 9.64/3.67  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 9.64/3.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.64/3.67  
% 9.85/3.70  tff(f_348, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 9.85/3.70  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 9.85/3.70  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.85/3.70  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.85/3.70  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 9.85/3.70  tff(f_208, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 9.85/3.70  tff(f_60, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 9.85/3.70  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 9.85/3.70  tff(f_212, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.85/3.70  tff(f_193, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 9.85/3.70  tff(f_286, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 9.85/3.70  tff(f_163, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 9.85/3.70  tff(f_131, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 9.85/3.70  tff(f_256, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 9.85/3.70  tff(f_104, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 9.85/3.70  tff(f_44, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 9.85/3.70  tff(f_318, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 9.85/3.70  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_71, plain, (![B_185, A_186]: (l1_pre_topc(B_185) | ~m1_pre_topc(B_185, A_186) | ~l1_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.85/3.70  tff(c_77, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_71])).
% 9.85/3.70  tff(c_81, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_77])).
% 9.85/3.70  tff(c_12, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.85/3.70  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.85/3.70  tff(c_95, plain, (![D_192]: (k1_funct_1('#skF_4', D_192)=D_192 | ~r2_hidden(D_192, u1_struct_0('#skF_3')) | ~m1_subset_1(D_192, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_100, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2, c_95])).
% 9.85/3.70  tff(c_102, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_100])).
% 9.85/3.70  tff(c_16, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.85/3.70  tff(c_105, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_102, c_16])).
% 9.85/3.70  tff(c_108, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_105])).
% 9.85/3.70  tff(c_111, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_108])).
% 9.85/3.70  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_111])).
% 9.85/3.70  tff(c_117, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_100])).
% 9.85/3.70  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_30, plain, (![A_77, B_78]: (m1_subset_1(k4_tmap_1(A_77, B_78), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_78), u1_struct_0(A_77)))) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.85/3.70  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_56, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_135, plain, (![A_202, B_203, D_204]: (r2_funct_2(A_202, B_203, D_204, D_204) | ~m1_subset_1(D_204, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))) | ~v1_funct_2(D_204, A_202, B_203) | ~v1_funct_1(D_204))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.85/3.70  tff(c_137, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_135])).
% 9.85/3.70  tff(c_140, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_137])).
% 9.85/3.70  tff(c_34, plain, (![A_77, B_78]: (v1_funct_1(k4_tmap_1(A_77, B_78)) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.85/3.70  tff(c_84, plain, (![B_190, A_191]: (v2_pre_topc(B_190) | ~m1_pre_topc(B_190, A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.85/3.70  tff(c_90, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_84])).
% 9.85/3.70  tff(c_94, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_90])).
% 9.85/3.70  tff(c_36, plain, (![A_79]: (m1_pre_topc(A_79, A_79) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_212])).
% 9.85/3.70  tff(c_166, plain, (![E_227, D_228, C_226, A_225, B_224]: (v1_funct_1(k3_tmap_1(A_225, B_224, C_226, D_228, E_227)) | ~m1_subset_1(E_227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_226), u1_struct_0(B_224)))) | ~v1_funct_2(E_227, u1_struct_0(C_226), u1_struct_0(B_224)) | ~v1_funct_1(E_227) | ~m1_pre_topc(D_228, A_225) | ~m1_pre_topc(C_226, A_225) | ~l1_pre_topc(B_224) | ~v2_pre_topc(B_224) | v2_struct_0(B_224) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.85/3.70  tff(c_170, plain, (![A_225, D_228]: (v1_funct_1(k3_tmap_1(A_225, '#skF_2', '#skF_3', D_228, '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_228, A_225) | ~m1_pre_topc('#skF_3', A_225) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(resolution, [status(thm)], [c_54, c_166])).
% 9.85/3.70  tff(c_174, plain, (![A_225, D_228]: (v1_funct_1(k3_tmap_1(A_225, '#skF_2', '#skF_3', D_228, '#skF_4')) | ~m1_pre_topc(D_228, A_225) | ~m1_pre_topc('#skF_3', A_225) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_170])).
% 9.85/3.70  tff(c_175, plain, (![A_225, D_228]: (v1_funct_1(k3_tmap_1(A_225, '#skF_2', '#skF_3', D_228, '#skF_4')) | ~m1_pre_topc(D_228, A_225) | ~m1_pre_topc('#skF_3', A_225) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(negUnitSimplification, [status(thm)], [c_68, c_174])).
% 9.85/3.70  tff(c_217, plain, (![B_250, C_252, D_254, E_253, A_251]: (v1_funct_2(k3_tmap_1(A_251, B_250, C_252, D_254, E_253), u1_struct_0(D_254), u1_struct_0(B_250)) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_252), u1_struct_0(B_250)))) | ~v1_funct_2(E_253, u1_struct_0(C_252), u1_struct_0(B_250)) | ~v1_funct_1(E_253) | ~m1_pre_topc(D_254, A_251) | ~m1_pre_topc(C_252, A_251) | ~l1_pre_topc(B_250) | ~v2_pre_topc(B_250) | v2_struct_0(B_250) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.85/3.70  tff(c_221, plain, (![A_251, D_254]: (v1_funct_2(k3_tmap_1(A_251, '#skF_2', '#skF_3', D_254, '#skF_4'), u1_struct_0(D_254), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_254, A_251) | ~m1_pre_topc('#skF_3', A_251) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_54, c_217])).
% 9.85/3.70  tff(c_225, plain, (![A_251, D_254]: (v1_funct_2(k3_tmap_1(A_251, '#skF_2', '#skF_3', D_254, '#skF_4'), u1_struct_0(D_254), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_254, A_251) | ~m1_pre_topc('#skF_3', A_251) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_221])).
% 9.85/3.70  tff(c_226, plain, (![A_251, D_254]: (v1_funct_2(k3_tmap_1(A_251, '#skF_2', '#skF_3', D_254, '#skF_4'), u1_struct_0(D_254), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_254, A_251) | ~m1_pre_topc('#skF_3', A_251) | ~l1_pre_topc(A_251) | ~v2_pre_topc(A_251) | v2_struct_0(A_251))), inference(negUnitSimplification, [status(thm)], [c_68, c_225])).
% 9.85/3.70  tff(c_236, plain, (![E_266, D_267, A_264, C_265, B_263]: (m1_subset_1(k3_tmap_1(A_264, B_263, C_265, D_267, E_266), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_267), u1_struct_0(B_263)))) | ~m1_subset_1(E_266, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_265), u1_struct_0(B_263)))) | ~v1_funct_2(E_266, u1_struct_0(C_265), u1_struct_0(B_263)) | ~v1_funct_1(E_266) | ~m1_pre_topc(D_267, A_264) | ~m1_pre_topc(C_265, A_264) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.85/3.70  tff(c_207, plain, (![C_246, B_247, D_248, A_249]: (r2_funct_2(u1_struct_0(C_246), u1_struct_0(B_247), D_248, k3_tmap_1(A_249, B_247, C_246, C_246, D_248)) | ~m1_subset_1(D_248, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_246), u1_struct_0(B_247)))) | ~v1_funct_2(D_248, u1_struct_0(C_246), u1_struct_0(B_247)) | ~v1_funct_1(D_248) | ~m1_pre_topc(C_246, A_249) | v2_struct_0(C_246) | ~l1_pre_topc(B_247) | ~v2_pre_topc(B_247) | v2_struct_0(B_247) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(cnfTransformation, [status(thm)], [f_286])).
% 9.85/3.70  tff(c_211, plain, (![A_249]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_249, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_249) | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(resolution, [status(thm)], [c_54, c_207])).
% 9.85/3.70  tff(c_215, plain, (![A_249]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_249, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_249) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249) | v2_struct_0(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_211])).
% 9.85/3.70  tff(c_227, plain, (![A_255]: (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_215])).
% 9.85/3.70  tff(c_8, plain, (![D_10, C_9, A_7, B_8]: (D_10=C_9 | ~r2_funct_2(A_7, B_8, C_9, D_10) | ~m1_subset_1(D_10, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(D_10, A_7, B_8) | ~v1_funct_1(D_10) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_2(C_9, A_7, B_8) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.85/3.70  tff(c_229, plain, (![A_255]: (k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(resolution, [status(thm)], [c_227, c_8])).
% 9.85/3.70  tff(c_232, plain, (![A_255]: (k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_subset_1(k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_255, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_229])).
% 9.85/3.70  tff(c_240, plain, (![A_264]: (k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', A_264) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(resolution, [status(thm)], [c_236, c_232])).
% 9.85/3.70  tff(c_255, plain, (![A_264]: (k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_264, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_264) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_240])).
% 9.85/3.70  tff(c_263, plain, (![A_268]: (k3_tmap_1(A_268, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_2(k3_tmap_1(A_268, '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1(A_268, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_268) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(negUnitSimplification, [status(thm)], [c_68, c_255])).
% 9.85/3.70  tff(c_269, plain, (![A_269]: (k3_tmap_1(A_269, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v1_funct_1(k3_tmap_1(A_269, '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', A_269) | ~l1_pre_topc(A_269) | ~v2_pre_topc(A_269) | v2_struct_0(A_269))), inference(resolution, [status(thm)], [c_226, c_263])).
% 9.85/3.70  tff(c_275, plain, (![A_270]: (k3_tmap_1(A_270, '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~m1_pre_topc('#skF_3', A_270) | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270) | v2_struct_0(A_270))), inference(resolution, [status(thm)], [c_175, c_269])).
% 9.85/3.70  tff(c_282, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_275])).
% 9.85/3.70  tff(c_289, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_282])).
% 9.85/3.70  tff(c_290, plain, (k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_68, c_289])).
% 9.85/3.70  tff(c_319, plain, (![A_271, C_274, D_275, E_272, B_273]: (k3_tmap_1(A_271, B_273, C_274, D_275, E_272)=k2_partfun1(u1_struct_0(C_274), u1_struct_0(B_273), E_272, u1_struct_0(D_275)) | ~m1_pre_topc(D_275, C_274) | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274), u1_struct_0(B_273)))) | ~v1_funct_2(E_272, u1_struct_0(C_274), u1_struct_0(B_273)) | ~v1_funct_1(E_272) | ~m1_pre_topc(D_275, A_271) | ~m1_pre_topc(C_274, A_271) | ~l1_pre_topc(B_273) | ~v2_pre_topc(B_273) | v2_struct_0(B_273) | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.85/3.70  tff(c_325, plain, (![A_271, D_275]: (k3_tmap_1(A_271, '#skF_2', '#skF_3', D_275, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_275)) | ~m1_pre_topc(D_275, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(D_275, A_271) | ~m1_pre_topc('#skF_3', A_271) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(resolution, [status(thm)], [c_54, c_319])).
% 9.85/3.70  tff(c_330, plain, (![A_271, D_275]: (k3_tmap_1(A_271, '#skF_2', '#skF_3', D_275, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_275)) | ~m1_pre_topc(D_275, '#skF_3') | ~m1_pre_topc(D_275, A_271) | ~m1_pre_topc('#skF_3', A_271) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_271) | ~v2_pre_topc(A_271) | v2_struct_0(A_271))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_325])).
% 9.85/3.70  tff(c_360, plain, (![A_276, D_277]: (k3_tmap_1(A_276, '#skF_2', '#skF_3', D_277, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_277)) | ~m1_pre_topc(D_277, '#skF_3') | ~m1_pre_topc(D_277, A_276) | ~m1_pre_topc('#skF_3', A_276) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(negUnitSimplification, [status(thm)], [c_68, c_330])).
% 9.85/3.70  tff(c_364, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_2', '#skF_3', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_60, c_360])).
% 9.85/3.70  tff(c_368, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_290, c_364])).
% 9.85/3.70  tff(c_369, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_368])).
% 9.85/3.70  tff(c_370, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_369])).
% 9.85/3.70  tff(c_373, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_370])).
% 9.85/3.70  tff(c_377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_373])).
% 9.85/3.70  tff(c_379, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_369])).
% 9.85/3.70  tff(c_378, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(splitRight, [status(thm)], [c_369])).
% 9.85/3.70  tff(c_188, plain, (![A_241, B_242, C_243, D_244]: (k2_partfun1(u1_struct_0(A_241), u1_struct_0(B_242), C_243, u1_struct_0(D_244))=k2_tmap_1(A_241, B_242, C_243, D_244) | ~m1_pre_topc(D_244, A_241) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_241), u1_struct_0(B_242)))) | ~v1_funct_2(C_243, u1_struct_0(A_241), u1_struct_0(B_242)) | ~v1_funct_1(C_243) | ~l1_pre_topc(B_242) | ~v2_pre_topc(B_242) | v2_struct_0(B_242) | ~l1_pre_topc(A_241) | ~v2_pre_topc(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.85/3.70  tff(c_192, plain, (![D_244]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_244))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_244) | ~m1_pre_topc(D_244, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_188])).
% 9.85/3.70  tff(c_196, plain, (![D_244]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_244))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_244) | ~m1_pre_topc(D_244, '#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_81, c_66, c_64, c_58, c_56, c_192])).
% 9.85/3.70  tff(c_197, plain, (![D_244]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(D_244))=k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_244) | ~m1_pre_topc(D_244, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_196])).
% 9.85/3.70  tff(c_411, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_378, c_197])).
% 9.85/3.70  tff(c_418, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_411])).
% 9.85/3.70  tff(c_646, plain, (![A_291, C_292, D_293, B_294, E_295]: (m1_subset_1('#skF_1'(A_291, C_292, D_293, B_294, E_295), u1_struct_0(B_294)) | r2_funct_2(u1_struct_0(C_292), u1_struct_0(A_291), k2_tmap_1(B_294, A_291, D_293, C_292), E_295) | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_292), u1_struct_0(A_291)))) | ~v1_funct_2(E_295, u1_struct_0(C_292), u1_struct_0(A_291)) | ~v1_funct_1(E_295) | ~m1_subset_1(D_293, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_294), u1_struct_0(A_291)))) | ~v1_funct_2(D_293, u1_struct_0(B_294), u1_struct_0(A_291)) | ~v1_funct_1(D_293) | ~m1_pre_topc(C_292, B_294) | v2_struct_0(C_292) | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_256])).
% 9.85/3.70  tff(c_1212, plain, (![A_357, B_358, D_359, B_360]: (m1_subset_1('#skF_1'(A_357, B_358, D_359, B_360, k4_tmap_1(A_357, B_358)), u1_struct_0(B_360)) | r2_funct_2(u1_struct_0(B_358), u1_struct_0(A_357), k2_tmap_1(B_360, A_357, D_359, B_358), k4_tmap_1(A_357, B_358)) | ~v1_funct_2(k4_tmap_1(A_357, B_358), u1_struct_0(B_358), u1_struct_0(A_357)) | ~v1_funct_1(k4_tmap_1(A_357, B_358)) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_360), u1_struct_0(A_357)))) | ~v1_funct_2(D_359, u1_struct_0(B_360), u1_struct_0(A_357)) | ~v1_funct_1(D_359) | ~m1_pre_topc(B_358, B_360) | v2_struct_0(B_358) | ~l1_pre_topc(B_360) | ~v2_pre_topc(B_360) | v2_struct_0(B_360) | ~m1_pre_topc(B_358, A_357) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357) | v2_struct_0(A_357))), inference(resolution, [status(thm)], [c_30, c_646])).
% 9.85/3.70  tff(c_1225, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_418, c_1212])).
% 9.85/3.70  tff(c_1231, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_94, c_81, c_379, c_58, c_56, c_54, c_1225])).
% 9.85/3.70  tff(c_1232, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1231])).
% 9.85/3.70  tff(c_1233, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1232])).
% 9.85/3.70  tff(c_1236, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_1233])).
% 9.85/3.70  tff(c_1239, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1236])).
% 9.85/3.70  tff(c_1241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1239])).
% 9.85/3.70  tff(c_1243, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1232])).
% 9.85/3.70  tff(c_32, plain, (![A_77, B_78]: (v1_funct_2(k4_tmap_1(A_77, B_78), u1_struct_0(B_78), u1_struct_0(A_77)) | ~m1_pre_topc(B_78, A_77) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_208])).
% 9.85/3.70  tff(c_1242, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1232])).
% 9.85/3.70  tff(c_1262, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1242])).
% 9.85/3.70  tff(c_1265, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1262])).
% 9.85/3.70  tff(c_1268, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1265])).
% 9.85/3.70  tff(c_1270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1268])).
% 9.85/3.70  tff(c_1272, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1242])).
% 9.85/3.70  tff(c_1271, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1242])).
% 9.85/3.70  tff(c_1273, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1271])).
% 9.85/3.70  tff(c_1275, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1273, c_8])).
% 9.85/3.70  tff(c_1278, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1243, c_1272, c_1275])).
% 9.85/3.70  tff(c_1289, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1278])).
% 9.85/3.70  tff(c_1292, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1289])).
% 9.85/3.70  tff(c_1295, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1292])).
% 9.85/3.70  tff(c_1297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1295])).
% 9.85/3.70  tff(c_1298, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1278])).
% 9.85/3.70  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_348])).
% 9.85/3.70  tff(c_1303, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_50])).
% 9.85/3.70  tff(c_1309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_1303])).
% 9.85/3.70  tff(c_1311, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1271])).
% 9.85/3.70  tff(c_279, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_36, c_275])).
% 9.85/3.70  tff(c_285, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_94, c_279])).
% 9.85/3.70  tff(c_286, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_285])).
% 9.85/3.70  tff(c_1310, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1271])).
% 9.85/3.70  tff(c_18, plain, (![C_25, A_19, B_23]: (m1_subset_1(C_25, u1_struct_0(A_19)) | ~m1_subset_1(C_25, u1_struct_0(B_23)) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_104])).
% 9.85/3.70  tff(c_1333, plain, (![A_19]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(A_19)) | ~m1_pre_topc('#skF_3', A_19) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(resolution, [status(thm)], [c_1310, c_18])).
% 9.85/3.70  tff(c_1344, plain, (![A_369]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(A_369)) | ~m1_pre_topc('#skF_3', A_369) | ~l1_pre_topc(A_369) | v2_struct_0(A_369))), inference(negUnitSimplification, [status(thm)], [c_62, c_1333])).
% 9.85/3.70  tff(c_116, plain, (![A_1]: (k1_funct_1('#skF_4', A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0('#skF_2')) | ~m1_subset_1(A_1, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_100])).
% 9.85/3.70  tff(c_1354, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1344, c_116])).
% 9.85/3.70  tff(c_1360, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1310, c_1354])).
% 9.85/3.70  tff(c_1361, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1360])).
% 9.85/3.70  tff(c_365, plain, (![A_79]: (k3_tmap_1(A_79, '#skF_2', '#skF_3', A_79, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_79)) | ~m1_pre_topc(A_79, '#skF_3') | ~m1_pre_topc('#skF_3', A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_36, c_360])).
% 9.85/3.70  tff(c_441, plain, (![A_283]: (k3_tmap_1(A_283, '#skF_2', '#skF_3', A_283, '#skF_4')=k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_283)) | ~m1_pre_topc(A_283, '#skF_3') | ~m1_pre_topc('#skF_3', A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283) | ~l1_pre_topc(A_283))), inference(resolution, [status(thm)], [c_36, c_360])).
% 9.85/3.70  tff(c_24, plain, (![B_73, C_74, E_76, A_72, D_75]: (m1_subset_1(k3_tmap_1(A_72, B_73, C_74, D_75, E_76), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_75), u1_struct_0(B_73)))) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_74), u1_struct_0(B_73)))) | ~v1_funct_2(E_76, u1_struct_0(C_74), u1_struct_0(B_73)) | ~v1_funct_1(E_76) | ~m1_pre_topc(D_75, A_72) | ~m1_pre_topc(C_74, A_72) | ~l1_pre_topc(B_73) | ~v2_pre_topc(B_73) | v2_struct_0(B_73) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.85/3.70  tff(c_453, plain, (![A_283]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_283)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283), u1_struct_0('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc(A_283, A_283) | ~m1_pre_topc('#skF_3', A_283) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283) | ~m1_pre_topc(A_283, '#skF_3') | ~m1_pre_topc('#skF_3', A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283) | ~l1_pre_topc(A_283))), inference(superposition, [status(thm), theory('equality')], [c_441, c_24])).
% 9.85/3.70  tff(c_481, plain, (![A_283]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_283)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_283), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_283, A_283) | v2_struct_0('#skF_2') | ~m1_pre_topc(A_283, '#skF_3') | ~m1_pre_topc('#skF_3', A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283) | ~l1_pre_topc(A_283))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_453])).
% 9.85/3.70  tff(c_502, plain, (![A_285]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', u1_struct_0(A_285)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_285), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_285, A_285) | ~m1_pre_topc(A_285, '#skF_3') | ~m1_pre_topc('#skF_3', A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285) | ~l1_pre_topc(A_285))), inference(negUnitSimplification, [status(thm)], [c_68, c_481])).
% 9.85/3.70  tff(c_521, plain, (![A_79]: (m1_subset_1(k3_tmap_1(A_79, '#skF_2', '#skF_3', A_79, '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_79), u1_struct_0('#skF_2')))) | ~m1_pre_topc(A_79, A_79) | ~m1_pre_topc(A_79, '#skF_3') | ~m1_pre_topc('#skF_3', A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79) | ~l1_pre_topc(A_79) | ~m1_pre_topc(A_79, '#skF_3') | ~m1_pre_topc('#skF_3', A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79) | ~l1_pre_topc(A_79))), inference(superposition, [status(thm), theory('equality')], [c_365, c_502])).
% 9.85/3.70  tff(c_4, plain, (![A_3, B_4, C_5, D_6]: (k3_funct_2(A_3, B_4, C_5, D_6)=k1_funct_1(C_5, D_6) | ~m1_subset_1(D_6, A_3) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~v1_funct_2(C_5, A_3, B_4) | ~v1_funct_1(C_5) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.85/3.70  tff(c_1331, plain, (![B_4, C_5]: (k3_funct_2(u1_struct_0('#skF_3'), B_4, C_5, '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))=k1_funct_1(C_5, '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_4))) | ~v1_funct_2(C_5, u1_struct_0('#skF_3'), B_4) | ~v1_funct_1(C_5) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1310, c_4])).
% 9.85/3.70  tff(c_1570, plain, (![B_389, C_390]: (k3_funct_2(u1_struct_0('#skF_3'), B_389, C_390, '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))=k1_funct_1(C_390, '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'))) | ~m1_subset_1(C_390, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_389))) | ~v1_funct_2(C_390, u1_struct_0('#skF_3'), B_389) | ~v1_funct_1(C_390))), inference(negUnitSimplification, [status(thm)], [c_117, c_1331])).
% 9.85/3.70  tff(c_1574, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))=k1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_3', '#skF_2', '#skF_3', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_521, c_1570])).
% 9.85/3.70  tff(c_1596, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_94, c_379, c_58, c_286, c_56, c_286, c_1361, c_286, c_286, c_1574])).
% 9.85/3.70  tff(c_1597, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_1596])).
% 9.85/3.70  tff(c_38, plain, (![E_140, C_128, D_136, A_80, B_112]: (k3_funct_2(u1_struct_0(B_112), u1_struct_0(A_80), D_136, '#skF_1'(A_80, C_128, D_136, B_112, E_140))!=k1_funct_1(E_140, '#skF_1'(A_80, C_128, D_136, B_112, E_140)) | r2_funct_2(u1_struct_0(C_128), u1_struct_0(A_80), k2_tmap_1(B_112, A_80, D_136, C_128), E_140) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_128), u1_struct_0(A_80)))) | ~v1_funct_2(E_140, u1_struct_0(C_128), u1_struct_0(A_80)) | ~v1_funct_1(E_140) | ~m1_subset_1(D_136, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_112), u1_struct_0(A_80)))) | ~v1_funct_2(D_136, u1_struct_0(B_112), u1_struct_0(A_80)) | ~v1_funct_1(D_136) | ~m1_pre_topc(C_128, B_112) | v2_struct_0(C_128) | ~l1_pre_topc(B_112) | ~v2_pre_topc(B_112) | v2_struct_0(B_112) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_256])).
% 9.85/3.70  tff(c_1613, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1597, c_38])).
% 9.85/3.70  tff(c_1617, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_94, c_81, c_379, c_58, c_56, c_54, c_1243, c_1272, c_418, c_1613])).
% 9.85/3.70  tff(c_1618, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1311, c_1617])).
% 9.85/3.70  tff(c_1623, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1618])).
% 9.85/3.70  tff(c_1626, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_1623])).
% 9.85/3.70  tff(c_1629, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1626])).
% 9.85/3.70  tff(c_1631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1629])).
% 9.85/3.70  tff(c_1632, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))!='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1618])).
% 9.85/3.70  tff(c_1366, plain, (![A_370, A_371]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(A_370)) | ~m1_pre_topc(A_371, A_370) | ~l1_pre_topc(A_370) | v2_struct_0(A_370) | ~m1_pre_topc('#skF_3', A_371) | ~l1_pre_topc(A_371) | v2_struct_0(A_371))), inference(resolution, [status(thm)], [c_1344, c_18])).
% 9.85/3.70  tff(c_1372, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1366])).
% 9.85/3.70  tff(c_1380, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_379, c_64, c_1372])).
% 9.85/3.70  tff(c_1381, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_1380])).
% 9.85/3.70  tff(c_146, plain, (![A_210, B_211, C_212]: (k1_funct_1(k4_tmap_1(A_210, B_211), C_212)=C_212 | ~r2_hidden(C_212, u1_struct_0(B_211)) | ~m1_subset_1(C_212, u1_struct_0(A_210)) | ~m1_pre_topc(B_211, A_210) | v2_struct_0(B_211) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210) | v2_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_318])).
% 9.85/3.70  tff(c_150, plain, (![A_210, B_211, A_1]: (k1_funct_1(k4_tmap_1(A_210, B_211), A_1)=A_1 | ~m1_subset_1(A_1, u1_struct_0(A_210)) | ~m1_pre_topc(B_211, A_210) | v2_struct_0(B_211) | ~l1_pre_topc(A_210) | ~v2_pre_topc(A_210) | v2_struct_0(A_210) | v1_xboole_0(u1_struct_0(B_211)) | ~m1_subset_1(A_1, u1_struct_0(B_211)))), inference(resolution, [status(thm)], [c_2, c_146])).
% 9.85/3.70  tff(c_1403, plain, (![B_211]: (k1_funct_1(k4_tmap_1('#skF_2', B_211), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc(B_211, '#skF_2') | v2_struct_0(B_211) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_211)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_211)))), inference(resolution, [status(thm)], [c_1381, c_150])).
% 9.85/3.70  tff(c_1413, plain, (![B_211]: (k1_funct_1(k4_tmap_1('#skF_2', B_211), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc(B_211, '#skF_2') | v2_struct_0(B_211) | v2_struct_0('#skF_2') | v1_xboole_0(u1_struct_0(B_211)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_211)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1403])).
% 9.85/3.70  tff(c_8461, plain, (![B_674]: (k1_funct_1(k4_tmap_1('#skF_2', B_674), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc(B_674, '#skF_2') | v2_struct_0(B_674) | v1_xboole_0(u1_struct_0(B_674)) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')), u1_struct_0(B_674)))), inference(negUnitSimplification, [status(thm)], [c_68, c_1413])).
% 9.85/3.70  tff(c_8477, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1310, c_8461])).
% 9.85/3.70  tff(c_8491, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')))='#skF_1'('#skF_2', '#skF_3', '#skF_4', '#skF_3', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8477])).
% 9.85/3.70  tff(c_8493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_62, c_1632, c_8491])).
% 9.85/3.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.85/3.70  
% 9.85/3.70  Inference rules
% 9.85/3.70  ----------------------
% 9.85/3.70  #Ref     : 0
% 9.85/3.70  #Sup     : 1542
% 9.85/3.70  #Fact    : 0
% 9.85/3.70  #Define  : 0
% 9.85/3.70  #Split   : 15
% 9.85/3.70  #Chain   : 0
% 9.85/3.70  #Close   : 0
% 9.85/3.70  
% 9.85/3.70  Ordering : KBO
% 9.85/3.70  
% 9.85/3.70  Simplification rules
% 9.85/3.70  ----------------------
% 9.85/3.70  #Subsume      : 333
% 9.85/3.70  #Demod        : 5159
% 9.85/3.70  #Tautology    : 531
% 9.85/3.70  #SimpNegUnit  : 840
% 9.85/3.70  #BackRed      : 106
% 9.85/3.70  
% 9.85/3.70  #Partial instantiations: 0
% 9.85/3.70  #Strategies tried      : 1
% 9.85/3.70  
% 9.85/3.70  Timing (in seconds)
% 9.85/3.70  ----------------------
% 9.85/3.70  Preprocessing        : 0.43
% 9.85/3.70  Parsing              : 0.22
% 9.85/3.70  CNF conversion       : 0.04
% 9.85/3.70  Main loop            : 2.44
% 9.85/3.70  Inferencing          : 0.74
% 9.85/3.70  Reduction            : 0.92
% 9.85/3.70  Demodulation         : 0.72
% 9.85/3.70  BG Simplification    : 0.08
% 9.85/3.70  Subsumption          : 0.58
% 9.85/3.70  Abstraction          : 0.14
% 9.85/3.70  MUC search           : 0.00
% 9.85/3.71  Cooper               : 0.00
% 9.85/3.71  Total                : 2.93
% 9.85/3.71  Index Insertion      : 0.00
% 9.85/3.71  Index Deletion       : 0.00
% 9.85/3.71  Index Matching       : 0.00
% 9.85/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
