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
% DateTime   : Thu Dec  3 10:27:46 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  345 (15360 expanded)
%              Number of leaves         :   39 (5841 expanded)
%              Depth                    :   34
%              Number of atoms          : 1224 (96156 expanded)
%              Number of equality atoms :   68 (5658 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_235,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_61,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_185,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_115,axiom,(
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

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_205,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_52,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_24,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k4_tmap_1(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_31),u1_struct_0(A_30))))
      | ~ m1_pre_topc(B_31,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_48,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_99,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_funct_2(A_139,B_140,D_141,D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140)))
      | ~ v1_funct_2(D_141,A_139,B_140)
      | ~ v1_funct_1(D_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_101,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_99])).

tff(c_104,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_101])).

tff(c_28,plain,(
    ! [A_30,B_31] :
      ( v1_funct_1(k4_tmap_1(A_30,B_31))
      | ~ m1_pre_topc(B_31,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_74,plain,(
    ! [B_121,A_122] :
      ( v2_pre_topc(B_121)
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_80,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_74])).

tff(c_84,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_80])).

tff(c_63,plain,(
    ! [B_119,A_120] :
      ( l1_pre_topc(B_119)
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_63])).

tff(c_73,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_69])).

tff(c_32,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_206,plain,(
    ! [A_190,B_189,D_193,C_191,E_192] :
      ( m1_subset_1('#skF_1'(B_189,A_190,C_191,E_192,D_193),u1_struct_0(B_189))
      | r2_funct_2(u1_struct_0(C_191),u1_struct_0(A_190),k2_tmap_1(B_189,A_190,D_193,C_191),E_192)
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191),u1_struct_0(A_190))))
      | ~ v1_funct_2(E_192,u1_struct_0(C_191),u1_struct_0(A_190))
      | ~ v1_funct_1(E_192)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_189),u1_struct_0(A_190))))
      | ~ v1_funct_2(D_193,u1_struct_0(B_189),u1_struct_0(A_190))
      | ~ v1_funct_1(D_193)
      | ~ m1_pre_topc(C_191,B_189)
      | v2_struct_0(C_191)
      | ~ l1_pre_topc(B_189)
      | ~ v2_pre_topc(B_189)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_212,plain,(
    ! [B_189,D_193] :
      ( m1_subset_1('#skF_1'(B_189,'#skF_2','#skF_3','#skF_4',D_193),u1_struct_0(B_189))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_189,'#skF_2',D_193,'#skF_3'),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_189),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_193,u1_struct_0(B_189),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_193)
      | ~ m1_pre_topc('#skF_3',B_189)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_189)
      | ~ v2_pre_topc(B_189)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_206])).

tff(c_217,plain,(
    ! [B_189,D_193] :
      ( m1_subset_1('#skF_1'(B_189,'#skF_2','#skF_3','#skF_4',D_193),u1_struct_0(B_189))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_189,'#skF_2',D_193,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_189),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_193,u1_struct_0(B_189),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_193)
      | ~ m1_pre_topc('#skF_3',B_189)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_189)
      | ~ v2_pre_topc(B_189)
      | v2_struct_0(B_189)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_48,c_212])).

tff(c_221,plain,(
    ! [B_201,D_202] :
      ( m1_subset_1('#skF_1'(B_201,'#skF_2','#skF_3','#skF_4',D_202),u1_struct_0(B_201))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_201,'#skF_2',D_202,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_201),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_202,u1_struct_0(B_201),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_202)
      | ~ m1_pre_topc('#skF_3',B_201)
      | ~ l1_pre_topc(B_201)
      | ~ v2_pre_topc(B_201)
      | v2_struct_0(B_201) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_217])).

tff(c_229,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_221])).

tff(c_239,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_73,c_50,c_48,c_229])).

tff(c_240,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_239])).

tff(c_241,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_244,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_244])).

tff(c_250,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_12,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_124,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( v1_funct_1(k2_tmap_1(A_154,B_155,C_156,D_157))
      | ~ l1_struct_0(D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_154),u1_struct_0(B_155))))
      | ~ v1_funct_2(C_156,u1_struct_0(A_154),u1_struct_0(B_155))
      | ~ v1_funct_1(C_156)
      | ~ l1_struct_0(B_155)
      | ~ l1_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_128,plain,(
    ! [D_157] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_157))
      | ~ l1_struct_0(D_157)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_124])).

tff(c_132,plain,(
    ! [D_157] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_157))
      | ~ l1_struct_0(D_157)
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_128])).

tff(c_133,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_136,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_136])).

tff(c_142,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_141,plain,(
    ! [D_157] :
      ( ~ l1_struct_0('#skF_2')
      | v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_157))
      | ~ l1_struct_0(D_157) ) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_143,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_153,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_143])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_153])).

tff(c_159,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_169,plain,(
    ! [A_167,B_168,C_169,D_170] :
      ( v1_funct_2(k2_tmap_1(A_167,B_168,C_169,D_170),u1_struct_0(D_170),u1_struct_0(B_168))
      | ~ l1_struct_0(D_170)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167),u1_struct_0(B_168))))
      | ~ v1_funct_2(C_169,u1_struct_0(A_167),u1_struct_0(B_168))
      | ~ v1_funct_1(C_169)
      | ~ l1_struct_0(B_168)
      | ~ l1_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_173,plain,(
    ! [D_170] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_170),u1_struct_0(D_170),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_170)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_46,c_169])).

tff(c_177,plain,(
    ! [D_170] :
      ( v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_170),u1_struct_0(D_170),u1_struct_0('#skF_2'))
      | ~ l1_struct_0(D_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_159,c_50,c_48,c_173])).

tff(c_18,plain,(
    ! [A_26,B_27,C_28,D_29] :
      ( m1_subset_1(k2_tmap_1(A_26,B_27,C_28,D_29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_29),u1_struct_0(B_27))))
      | ~ l1_struct_0(D_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_26),u1_struct_0(B_27))))
      | ~ v1_funct_2(C_28,u1_struct_0(A_26),u1_struct_0(B_27))
      | ~ v1_funct_1(C_28)
      | ~ l1_struct_0(B_27)
      | ~ l1_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_158,plain,(
    ! [D_157] :
      ( v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4',D_157))
      | ~ l1_struct_0(D_157) ) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_251,plain,(
    ! [E_206,B_203,D_207,C_205,A_204] :
      ( r2_hidden('#skF_1'(B_203,A_204,C_205,E_206,D_207),u1_struct_0(C_205))
      | r2_funct_2(u1_struct_0(C_205),u1_struct_0(A_204),k2_tmap_1(B_203,A_204,D_207,C_205),E_206)
      | ~ m1_subset_1(E_206,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_205),u1_struct_0(A_204))))
      | ~ v1_funct_2(E_206,u1_struct_0(C_205),u1_struct_0(A_204))
      | ~ v1_funct_1(E_206)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_203),u1_struct_0(A_204))))
      | ~ v1_funct_2(D_207,u1_struct_0(B_203),u1_struct_0(A_204))
      | ~ v1_funct_1(D_207)
      | ~ m1_pre_topc(C_205,B_203)
      | v2_struct_0(C_205)
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_257,plain,(
    ! [B_203,D_207] :
      ( r2_hidden('#skF_1'(B_203,'#skF_2','#skF_3','#skF_4',D_207),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_203,'#skF_2',D_207,'#skF_3'),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_203),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_207,u1_struct_0(B_203),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_207)
      | ~ m1_pre_topc('#skF_3',B_203)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_251])).

tff(c_262,plain,(
    ! [B_203,D_207] :
      ( r2_hidden('#skF_1'(B_203,'#skF_2','#skF_3','#skF_4',D_207),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_203,'#skF_2',D_207,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_203),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_207,u1_struct_0(B_203),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_207)
      | ~ m1_pre_topc('#skF_3',B_203)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_203)
      | ~ v2_pre_topc(B_203)
      | v2_struct_0(B_203)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_50,c_48,c_257])).

tff(c_1350,plain,(
    ! [B_357,D_358] :
      ( r2_hidden('#skF_1'(B_357,'#skF_2','#skF_3','#skF_4',D_358),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_357,'#skF_2',D_358,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_357),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_358,u1_struct_0(B_357),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_358)
      | ~ m1_pre_topc('#skF_3',B_357)
      | ~ l1_pre_topc(B_357)
      | ~ v2_pre_topc(B_357)
      | v2_struct_0(B_357) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_262])).

tff(c_1361,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1350])).

tff(c_1371,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_73,c_250,c_50,c_48,c_1361])).

tff(c_1372,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1371])).

tff(c_1373,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1372])).

tff(c_8,plain,(
    ! [D_11,C_10,A_8,B_9] :
      ( D_11 = C_10
      | ~ r2_funct_2(A_8,B_9,C_10,D_11)
      | ~ m1_subset_1(D_11,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(D_11,A_8,B_9)
      | ~ v1_funct_1(D_11)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1375,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1373,c_8])).

tff(c_1378,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1375])).

tff(c_1402,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1378])).

tff(c_1412,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_1402])).

tff(c_1416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1412])).

tff(c_1417,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_1419,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1417])).

tff(c_1428,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1419])).

tff(c_1432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_159,c_50,c_48,c_46,c_1428])).

tff(c_1433,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1417])).

tff(c_1488,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1433])).

tff(c_1491,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_1488])).

tff(c_1495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_1491])).

tff(c_1496,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1433])).

tff(c_2071,plain,(
    ! [B_482,A_483,B_484,D_485] :
      ( r2_hidden('#skF_1'(B_482,A_483,B_484,k4_tmap_1(A_483,B_484),D_485),u1_struct_0(B_484))
      | r2_funct_2(u1_struct_0(B_484),u1_struct_0(A_483),k2_tmap_1(B_482,A_483,D_485,B_484),k4_tmap_1(A_483,B_484))
      | ~ v1_funct_2(k4_tmap_1(A_483,B_484),u1_struct_0(B_484),u1_struct_0(A_483))
      | ~ v1_funct_1(k4_tmap_1(A_483,B_484))
      | ~ m1_subset_1(D_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_482),u1_struct_0(A_483))))
      | ~ v1_funct_2(D_485,u1_struct_0(B_482),u1_struct_0(A_483))
      | ~ v1_funct_1(D_485)
      | ~ m1_pre_topc(B_484,B_482)
      | v2_struct_0(B_484)
      | ~ l1_pre_topc(B_482)
      | ~ v2_pre_topc(B_482)
      | v2_struct_0(B_482)
      | ~ m1_pre_topc(B_484,A_483)
      | ~ l1_pre_topc(A_483)
      | ~ v2_pre_topc(A_483)
      | v2_struct_0(A_483) ) ),
    inference(resolution,[status(thm)],[c_24,c_251])).

tff(c_2076,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_2071])).

tff(c_2079,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_2076])).

tff(c_2080,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2079])).

tff(c_2081,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2080])).

tff(c_2084,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_2081])).

tff(c_2087,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2084])).

tff(c_2089,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2087])).

tff(c_2091,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2080])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( v1_funct_2(k4_tmap_1(A_30,B_31),u1_struct_0(B_31),u1_struct_0(A_30))
      | ~ m1_pre_topc(B_31,A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2090,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2080])).

tff(c_2094,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2090])).

tff(c_2097,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2094])).

tff(c_2100,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2097])).

tff(c_2102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2100])).

tff(c_2104,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2090])).

tff(c_2103,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2090])).

tff(c_2105,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2103])).

tff(c_2107,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2105,c_8])).

tff(c_2110,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_2091,c_2104,c_2107])).

tff(c_2112,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2110])).

tff(c_2115,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2112])).

tff(c_2118,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2115])).

tff(c_2120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2118])).

tff(c_2121,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2110])).

tff(c_42,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_2126,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2121,c_42])).

tff(c_2132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2126])).

tff(c_2134,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2103])).

tff(c_2159,plain,(
    ! [B_495,A_496,B_497,D_498] :
      ( m1_subset_1('#skF_1'(B_495,A_496,B_497,k4_tmap_1(A_496,B_497),D_498),u1_struct_0(B_495))
      | r2_funct_2(u1_struct_0(B_497),u1_struct_0(A_496),k2_tmap_1(B_495,A_496,D_498,B_497),k4_tmap_1(A_496,B_497))
      | ~ v1_funct_2(k4_tmap_1(A_496,B_497),u1_struct_0(B_497),u1_struct_0(A_496))
      | ~ v1_funct_1(k4_tmap_1(A_496,B_497))
      | ~ m1_subset_1(D_498,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_495),u1_struct_0(A_496))))
      | ~ v1_funct_2(D_498,u1_struct_0(B_495),u1_struct_0(A_496))
      | ~ v1_funct_1(D_498)
      | ~ m1_pre_topc(B_497,B_495)
      | v2_struct_0(B_497)
      | ~ l1_pre_topc(B_495)
      | ~ v2_pre_topc(B_495)
      | v2_struct_0(B_495)
      | ~ m1_pre_topc(B_497,A_496)
      | ~ l1_pre_topc(A_496)
      | ~ v2_pre_topc(A_496)
      | v2_struct_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_24,c_206])).

tff(c_2168,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_2159])).

tff(c_2173,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_2091,c_2104,c_2168])).

tff(c_2174,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2134,c_2173])).

tff(c_16,plain,(
    ! [C_25,A_19,B_23] :
      ( m1_subset_1(C_25,u1_struct_0(A_19))
      | ~ m1_subset_1(C_25,u1_struct_0(B_23))
      | ~ m1_pre_topc(B_23,A_19)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2178,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_19))
      | ~ m1_pre_topc('#skF_3',A_19)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_2174,c_16])).

tff(c_2190,plain,(
    ! [A_499] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_499))
      | ~ m1_pre_topc('#skF_3',A_499)
      | ~ l1_pre_topc(A_499)
      | v2_struct_0(A_499) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2178])).

tff(c_2133,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2103])).

tff(c_44,plain,(
    ! [D_116] :
      ( k1_funct_1('#skF_4',D_116) = D_116
      | ~ r2_hidden(D_116,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_116,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_2156,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2133,c_44])).

tff(c_2157,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2156])).

tff(c_2193,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2190,c_2157])).

tff(c_2200,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2193])).

tff(c_2202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2200])).

tff(c_2204,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2156])).

tff(c_40,plain,(
    ! [A_98,B_102,C_104] :
      ( k1_funct_1(k4_tmap_1(A_98,B_102),C_104) = C_104
      | ~ r2_hidden(C_104,u1_struct_0(B_102))
      | ~ m1_subset_1(C_104,u1_struct_0(A_98))
      | ~ m1_pre_topc(B_102,A_98)
      | v2_struct_0(B_102)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_2149,plain,(
    ! [A_98] :
      ( k1_funct_1(k4_tmap_1(A_98,'#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_98))
      | ~ m1_pre_topc('#skF_3',A_98)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_2133,c_40])).

tff(c_2282,plain,(
    ! [A_508] :
      ( k1_funct_1(k4_tmap_1(A_508,'#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_508))
      | ~ m1_pre_topc('#skF_3',A_508)
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2149])).

tff(c_2296,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2204,c_2282])).

tff(c_2305,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2296])).

tff(c_2306,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2305])).

tff(c_2203,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2156])).

tff(c_788,plain,(
    ! [B_282,D_283] :
      ( r2_hidden('#skF_1'(B_282,'#skF_2','#skF_3','#skF_4',D_283),u1_struct_0('#skF_3'))
      | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1(B_282,'#skF_2',D_283,'#skF_3'),'#skF_4')
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_282),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_283,u1_struct_0(B_282),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_283)
      | ~ m1_pre_topc('#skF_3',B_282)
      | ~ l1_pre_topc(B_282)
      | ~ v2_pre_topc(B_282)
      | v2_struct_0(B_282) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_262])).

tff(c_799,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_788])).

tff(c_809,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_73,c_250,c_50,c_48,c_799])).

tff(c_810,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_809])).

tff(c_811,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_810])).

tff(c_813,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_811,c_8])).

tff(c_816,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_813])).

tff(c_817,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_816])).

tff(c_826,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_817])).

tff(c_830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_826])).

tff(c_831,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_816])).

tff(c_833,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_831])).

tff(c_836,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_833])).

tff(c_840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_159,c_50,c_48,c_46,c_836])).

tff(c_841,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_831])).

tff(c_899,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_841])).

tff(c_902,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_899])).

tff(c_906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_902])).

tff(c_907,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_841])).

tff(c_1051,plain,(
    ! [B_316,A_317,B_318,D_319] :
      ( m1_subset_1('#skF_1'(B_316,A_317,B_318,k4_tmap_1(A_317,B_318),D_319),u1_struct_0(B_316))
      | r2_funct_2(u1_struct_0(B_318),u1_struct_0(A_317),k2_tmap_1(B_316,A_317,D_319,B_318),k4_tmap_1(A_317,B_318))
      | ~ v1_funct_2(k4_tmap_1(A_317,B_318),u1_struct_0(B_318),u1_struct_0(A_317))
      | ~ v1_funct_1(k4_tmap_1(A_317,B_318))
      | ~ m1_subset_1(D_319,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_316),u1_struct_0(A_317))))
      | ~ v1_funct_2(D_319,u1_struct_0(B_316),u1_struct_0(A_317))
      | ~ v1_funct_1(D_319)
      | ~ m1_pre_topc(B_318,B_316)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(B_316)
      | ~ v2_pre_topc(B_316)
      | v2_struct_0(B_316)
      | ~ m1_pre_topc(B_318,A_317)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(resolution,[status(thm)],[c_24,c_206])).

tff(c_1060,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_907,c_1051])).

tff(c_1065,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_1060])).

tff(c_1066,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1065])).

tff(c_1067,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1066])).

tff(c_1070,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_1067])).

tff(c_1073,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_1070])).

tff(c_1075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1073])).

tff(c_1077,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1066])).

tff(c_1076,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1066])).

tff(c_1080,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1076])).

tff(c_1083,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_1080])).

tff(c_1086,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_1083])).

tff(c_1088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1086])).

tff(c_1090,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1076])).

tff(c_1089,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1076])).

tff(c_1091,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1089])).

tff(c_1093,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1091,c_8])).

tff(c_1096,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1077,c_1090,c_1093])).

tff(c_1107,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1096])).

tff(c_1110,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1107])).

tff(c_1113,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_1110])).

tff(c_1115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1113])).

tff(c_1116,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1096])).

tff(c_1121,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_42])).

tff(c_1127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1121])).

tff(c_1129,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1089])).

tff(c_1312,plain,(
    ! [B_353,A_354,B_355,D_356] :
      ( r2_hidden('#skF_1'(B_353,A_354,B_355,k4_tmap_1(A_354,B_355),D_356),u1_struct_0(B_355))
      | r2_funct_2(u1_struct_0(B_355),u1_struct_0(A_354),k2_tmap_1(B_353,A_354,D_356,B_355),k4_tmap_1(A_354,B_355))
      | ~ v1_funct_2(k4_tmap_1(A_354,B_355),u1_struct_0(B_355),u1_struct_0(A_354))
      | ~ v1_funct_1(k4_tmap_1(A_354,B_355))
      | ~ m1_subset_1(D_356,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_353),u1_struct_0(A_354))))
      | ~ v1_funct_2(D_356,u1_struct_0(B_353),u1_struct_0(A_354))
      | ~ v1_funct_1(D_356)
      | ~ m1_pre_topc(B_355,B_353)
      | v2_struct_0(B_355)
      | ~ l1_pre_topc(B_353)
      | ~ v2_pre_topc(B_353)
      | v2_struct_0(B_353)
      | ~ m1_pre_topc(B_355,A_354)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354)
      | v2_struct_0(A_354) ) ),
    inference(resolution,[status(thm)],[c_24,c_251])).

tff(c_1317,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_907,c_1312])).

tff(c_1320,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_1077,c_1090,c_1317])).

tff(c_1321,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_1129,c_1320])).

tff(c_249,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_276,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6,D_7] :
      ( k3_funct_2(A_4,B_5,C_6,D_7) = k1_funct_1(C_6,D_7)
      | ~ m1_subset_1(D_7,A_4)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5)))
      | ~ v1_funct_2(C_6,A_4,B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_281,plain,(
    ! [B_5,C_6] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_5,C_6,'#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')) = k1_funct_1(C_6,'#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_5)))
      | ~ v1_funct_2(C_6,u1_struct_0('#skF_3'),B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_276,c_4])).

tff(c_339,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_90,plain,(
    ! [B_126,A_127] :
      ( m1_subset_1(u1_struct_0(B_126),k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ m1_pre_topc(B_126,A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( ~ v1_xboole_0(C_3)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(C_3))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_93,plain,(
    ! [A_127,A_1,B_126] :
      ( ~ v1_xboole_0(u1_struct_0(A_127))
      | ~ r2_hidden(A_1,u1_struct_0(B_126))
      | ~ m1_pre_topc(B_126,A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_342,plain,(
    ! [A_1,B_126] :
      ( ~ r2_hidden(A_1,u1_struct_0(B_126))
      | ~ m1_pre_topc(B_126,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_339,c_93])).

tff(c_345,plain,(
    ! [A_1,B_126] :
      ( ~ r2_hidden(A_1,u1_struct_0(B_126))
      | ~ m1_pre_topc(B_126,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_342])).

tff(c_1324,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1321,c_345])).

tff(c_1333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_1324])).

tff(c_1334,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_810])).

tff(c_1338,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1334,c_345])).

tff(c_1347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_1338])).

tff(c_1349,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2248,plain,(
    ! [B_503,A_504,B_505,D_506] :
      ( m1_subset_1('#skF_1'(B_503,A_504,B_505,k4_tmap_1(A_504,B_505),D_506),u1_struct_0(B_503))
      | r2_funct_2(u1_struct_0(B_505),u1_struct_0(A_504),k2_tmap_1(B_503,A_504,D_506,B_505),k4_tmap_1(A_504,B_505))
      | ~ v1_funct_2(k4_tmap_1(A_504,B_505),u1_struct_0(B_505),u1_struct_0(A_504))
      | ~ v1_funct_1(k4_tmap_1(A_504,B_505))
      | ~ m1_subset_1(D_506,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_503),u1_struct_0(A_504))))
      | ~ v1_funct_2(D_506,u1_struct_0(B_503),u1_struct_0(A_504))
      | ~ v1_funct_1(D_506)
      | ~ m1_pre_topc(B_505,B_503)
      | v2_struct_0(B_505)
      | ~ l1_pre_topc(B_503)
      | ~ v2_pre_topc(B_503)
      | v2_struct_0(B_503)
      | ~ m1_pre_topc(B_505,A_504)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(resolution,[status(thm)],[c_24,c_206])).

tff(c_2257,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_2248])).

tff(c_2262,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_2091,c_2104,c_2257])).

tff(c_2263,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2134,c_2262])).

tff(c_2265,plain,(
    ! [B_5,C_6] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_5,C_6,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(C_6,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_5)))
      | ~ v1_funct_2(C_6,u1_struct_0('#skF_3'),B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2263,c_4])).

tff(c_2369,plain,(
    ! [B_518,C_519] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_518,C_519,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(C_519,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ m1_subset_1(C_519,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_518)))
      | ~ v1_funct_2(C_519,u1_struct_0('#skF_3'),B_518)
      | ~ v1_funct_1(C_519) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1349,c_2265])).

tff(c_2380,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2369])).

tff(c_2387,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2203,c_2380])).

tff(c_34,plain,(
    ! [D_92,A_36,C_84,B_68,E_96] :
      ( k3_funct_2(u1_struct_0(B_68),u1_struct_0(A_36),D_92,'#skF_1'(B_68,A_36,C_84,E_96,D_92)) != k1_funct_1(E_96,'#skF_1'(B_68,A_36,C_84,E_96,D_92))
      | r2_funct_2(u1_struct_0(C_84),u1_struct_0(A_36),k2_tmap_1(B_68,A_36,D_92,C_84),E_96)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_84),u1_struct_0(A_36))))
      | ~ v1_funct_2(E_96,u1_struct_0(C_84),u1_struct_0(A_36))
      | ~ v1_funct_1(E_96)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_68),u1_struct_0(A_36))))
      | ~ v1_funct_2(D_92,u1_struct_0(B_68),u1_struct_0(A_36))
      | ~ v1_funct_1(D_92)
      | ~ m1_pre_topc(C_84,B_68)
      | v2_struct_0(C_84)
      | ~ l1_pre_topc(B_68)
      | ~ v2_pre_topc(B_68)
      | v2_struct_0(B_68)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2390,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
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
    inference(superposition,[status(thm),theory(equality)],[c_2387,c_34])).

tff(c_2394,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_84,c_73,c_250,c_50,c_48,c_46,c_2091,c_2104,c_1496,c_2306,c_2390])).

tff(c_2395,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2134,c_2394])).

tff(c_2399,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2395])).

tff(c_2402,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2399])).

tff(c_2404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2402])).

tff(c_2406,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1372])).

tff(c_280,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0(A_19))
      | ~ m1_pre_topc('#skF_3',A_19)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_276,c_16])).

tff(c_285,plain,(
    ! [A_208] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0(A_208))
      | ~ m1_pre_topc('#skF_3',A_208)
      | ~ l1_pre_topc(A_208)
      | v2_struct_0(A_208) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_280])).

tff(c_292,plain,(
    ! [A_209,A_210] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0(A_209))
      | ~ m1_pre_topc(A_210,A_209)
      | ~ l1_pre_topc(A_209)
      | v2_struct_0(A_209)
      | ~ m1_pre_topc('#skF_3',A_210)
      | ~ l1_pre_topc(A_210)
      | v2_struct_0(A_210) ) ),
    inference(resolution,[status(thm)],[c_285,c_16])).

tff(c_298,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_292])).

tff(c_306,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_250,c_56,c_298])).

tff(c_307,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60,c_306])).

tff(c_2405,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1372])).

tff(c_2417,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2405,c_44])).

tff(c_2423,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_2417])).

tff(c_2428,plain,(
    ! [B_521,C_522] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_521,C_522,'#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')) = k1_funct_1(C_522,'#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'))
      | ~ m1_subset_1(C_522,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_521)))
      | ~ v1_funct_2(C_522,u1_struct_0('#skF_3'),B_521)
      | ~ v1_funct_1(C_522) ) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_2439,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2428])).

tff(c_2446,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2423,c_2439])).

tff(c_2451,plain,(
    ! [D_527,C_525,E_526,B_523,A_524] :
      ( k3_funct_2(u1_struct_0(B_523),u1_struct_0(A_524),D_527,'#skF_1'(B_523,A_524,C_525,E_526,D_527)) != k1_funct_1(E_526,'#skF_1'(B_523,A_524,C_525,E_526,D_527))
      | r2_funct_2(u1_struct_0(C_525),u1_struct_0(A_524),k2_tmap_1(B_523,A_524,D_527,C_525),E_526)
      | ~ m1_subset_1(E_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_525),u1_struct_0(A_524))))
      | ~ v1_funct_2(E_526,u1_struct_0(C_525),u1_struct_0(A_524))
      | ~ v1_funct_1(E_526)
      | ~ m1_subset_1(D_527,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_523),u1_struct_0(A_524))))
      | ~ v1_funct_2(D_527,u1_struct_0(B_523),u1_struct_0(A_524))
      | ~ v1_funct_1(D_527)
      | ~ m1_pre_topc(C_525,B_523)
      | v2_struct_0(C_525)
      | ~ l1_pre_topc(B_523)
      | ~ v2_pre_topc(B_523)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_2453,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')) != '#skF_1'('#skF_3','#skF_2','#skF_3','#skF_4','#skF_4')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
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
    inference(superposition,[status(thm),theory(equality)],[c_2446,c_2451])).

tff(c_2455,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_84,c_73,c_250,c_50,c_48,c_46,c_50,c_48,c_46,c_2423,c_2453])).

tff(c_2457,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2406,c_2455])).

tff(c_2458,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_2461,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2458,c_8])).

tff(c_2464,plain,
    ( k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_2461])).

tff(c_2465,plain,(
    ~ v1_funct_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2464])).

tff(c_2491,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_158,c_2465])).

tff(c_2495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2491])).

tff(c_2496,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2464])).

tff(c_2498,plain,(
    ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2496])).

tff(c_2501,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2498])).

tff(c_2505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_159,c_50,c_48,c_46,c_2501])).

tff(c_2506,plain,
    ( ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2496])).

tff(c_2549,plain,(
    ~ v1_funct_2(k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2506])).

tff(c_2552,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_177,c_2549])).

tff(c_2556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_2552])).

tff(c_2557,plain,(
    k2_tmap_1('#skF_3','#skF_2','#skF_4','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2506])).

tff(c_2697,plain,(
    ! [B_565,A_566,B_567,D_568] :
      ( r2_hidden('#skF_1'(B_565,A_566,B_567,k4_tmap_1(A_566,B_567),D_568),u1_struct_0(B_567))
      | r2_funct_2(u1_struct_0(B_567),u1_struct_0(A_566),k2_tmap_1(B_565,A_566,D_568,B_567),k4_tmap_1(A_566,B_567))
      | ~ v1_funct_2(k4_tmap_1(A_566,B_567),u1_struct_0(B_567),u1_struct_0(A_566))
      | ~ v1_funct_1(k4_tmap_1(A_566,B_567))
      | ~ m1_subset_1(D_568,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_565),u1_struct_0(A_566))))
      | ~ v1_funct_2(D_568,u1_struct_0(B_565),u1_struct_0(A_566))
      | ~ v1_funct_1(D_568)
      | ~ m1_pre_topc(B_567,B_565)
      | v2_struct_0(B_567)
      | ~ l1_pre_topc(B_565)
      | ~ v2_pre_topc(B_565)
      | v2_struct_0(B_565)
      | ~ m1_pre_topc(B_567,A_566)
      | ~ l1_pre_topc(A_566)
      | ~ v2_pre_topc(A_566)
      | v2_struct_0(A_566) ) ),
    inference(resolution,[status(thm)],[c_24,c_251])).

tff(c_2702,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_2557,c_2697])).

tff(c_2705,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_2702])).

tff(c_2706,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2705])).

tff(c_2707,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2706])).

tff(c_2710,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_2707])).

tff(c_2713,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2710])).

tff(c_2715,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2713])).

tff(c_2717,plain,(
    v1_funct_1(k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2706])).

tff(c_2716,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2706])).

tff(c_2720,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2716])).

tff(c_2723,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2720])).

tff(c_2726,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2723])).

tff(c_2728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2726])).

tff(c_2730,plain,(
    v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2716])).

tff(c_2729,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2716])).

tff(c_2731,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2729])).

tff(c_2733,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2731,c_8])).

tff(c_2736,plain,
    ( k4_tmap_1('#skF_2','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_2717,c_2730,c_2733])).

tff(c_2738,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2736])).

tff(c_2741,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2738])).

tff(c_2744,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_2741])).

tff(c_2746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2744])).

tff(c_2747,plain,(
    k4_tmap_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2736])).

tff(c_2752,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2747,c_42])).

tff(c_2758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2752])).

tff(c_2760,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2729])).

tff(c_2836,plain,(
    ! [B_588,A_589,B_590,D_591] :
      ( m1_subset_1('#skF_1'(B_588,A_589,B_590,k4_tmap_1(A_589,B_590),D_591),u1_struct_0(B_588))
      | r2_funct_2(u1_struct_0(B_590),u1_struct_0(A_589),k2_tmap_1(B_588,A_589,D_591,B_590),k4_tmap_1(A_589,B_590))
      | ~ v1_funct_2(k4_tmap_1(A_589,B_590),u1_struct_0(B_590),u1_struct_0(A_589))
      | ~ v1_funct_1(k4_tmap_1(A_589,B_590))
      | ~ m1_subset_1(D_591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_588),u1_struct_0(A_589))))
      | ~ v1_funct_2(D_591,u1_struct_0(B_588),u1_struct_0(A_589))
      | ~ v1_funct_1(D_591)
      | ~ m1_pre_topc(B_590,B_588)
      | v2_struct_0(B_590)
      | ~ l1_pre_topc(B_588)
      | ~ v2_pre_topc(B_588)
      | v2_struct_0(B_588)
      | ~ m1_pre_topc(B_590,A_589)
      | ~ l1_pre_topc(A_589)
      | ~ v2_pre_topc(A_589)
      | v2_struct_0(A_589) ) ),
    inference(resolution,[status(thm)],[c_24,c_206])).

tff(c_2847,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_2557,c_2836])).

tff(c_2852,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_2717,c_2730,c_2847])).

tff(c_2853,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2760,c_2852])).

tff(c_2860,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_19))
      | ~ m1_pre_topc('#skF_3',A_19)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_2853,c_16])).

tff(c_2922,plain,(
    ! [A_592] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_592))
      | ~ m1_pre_topc('#skF_3',A_592)
      | ~ l1_pre_topc(A_592)
      | v2_struct_0(A_592) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2860])).

tff(c_2759,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2729])).

tff(c_2782,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2759,c_44])).

tff(c_2783,plain,(
    ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2782])).

tff(c_2928,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2922,c_2783])).

tff(c_2936,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_2928])).

tff(c_2938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2936])).

tff(c_2940,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2782])).

tff(c_2775,plain,(
    ! [A_98] :
      ( k1_funct_1(k4_tmap_1(A_98,'#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_98))
      | ~ m1_pre_topc('#skF_3',A_98)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_2759,c_40])).

tff(c_3014,plain,(
    ! [A_601] :
      ( k1_funct_1(k4_tmap_1(A_601,'#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_601))
      | ~ m1_pre_topc('#skF_3',A_601)
      | ~ l1_pre_topc(A_601)
      | ~ v2_pre_topc(A_601)
      | v2_struct_0(A_601) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2775])).

tff(c_3028,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2940,c_3014])).

tff(c_3037,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_3028])).

tff(c_3038,plain,(
    k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3037])).

tff(c_2982,plain,(
    ! [B_596,A_597,B_598,D_599] :
      ( m1_subset_1('#skF_1'(B_596,A_597,B_598,k4_tmap_1(A_597,B_598),D_599),u1_struct_0(B_596))
      | r2_funct_2(u1_struct_0(B_598),u1_struct_0(A_597),k2_tmap_1(B_596,A_597,D_599,B_598),k4_tmap_1(A_597,B_598))
      | ~ v1_funct_2(k4_tmap_1(A_597,B_598),u1_struct_0(B_598),u1_struct_0(A_597))
      | ~ v1_funct_1(k4_tmap_1(A_597,B_598))
      | ~ m1_subset_1(D_599,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_596),u1_struct_0(A_597))))
      | ~ v1_funct_2(D_599,u1_struct_0(B_596),u1_struct_0(A_597))
      | ~ v1_funct_1(D_599)
      | ~ m1_pre_topc(B_598,B_596)
      | v2_struct_0(B_598)
      | ~ l1_pre_topc(B_596)
      | ~ v2_pre_topc(B_596)
      | v2_struct_0(B_596)
      | ~ m1_pre_topc(B_598,A_597)
      | ~ l1_pre_topc(A_597)
      | ~ v2_pre_topc(A_597)
      | v2_struct_0(A_597) ) ),
    inference(resolution,[status(thm)],[c_24,c_206])).

tff(c_2991,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
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
    inference(superposition,[status(thm),theory(equality)],[c_2557,c_2982])).

tff(c_2996,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_84,c_73,c_250,c_50,c_48,c_46,c_2717,c_2730,c_2991])).

tff(c_2997,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2760,c_2996])).

tff(c_3002,plain,(
    ! [B_5,C_6] :
      ( k3_funct_2(u1_struct_0('#skF_3'),B_5,C_6,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(C_6,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),B_5)))
      | ~ v1_funct_2(C_6,u1_struct_0('#skF_3'),B_5)
      | ~ v1_funct_1(C_6)
      | v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_2997,c_4])).

tff(c_3101,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3002])).

tff(c_3103,plain,(
    ! [A_1,B_126] :
      ( ~ r2_hidden(A_1,u1_struct_0(B_126))
      | ~ m1_pre_topc(B_126,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3101,c_93])).

tff(c_3107,plain,(
    ! [A_611,B_612] :
      ( ~ r2_hidden(A_611,u1_struct_0(B_612))
      | ~ m1_pre_topc(B_612,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_3103])).

tff(c_3110,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_2759,c_3107])).

tff(c_3114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_3110])).

tff(c_3116,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3002])).

tff(c_2939,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2782])).

tff(c_3001,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_19))
      | ~ m1_pre_topc('#skF_3',A_19)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(resolution,[status(thm)],[c_2997,c_16])).

tff(c_3007,plain,(
    ! [A_600] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'),u1_struct_0(A_600))
      | ~ m1_pre_topc('#skF_3',A_600)
      | ~ l1_pre_topc(A_600)
      | v2_struct_0(A_600) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3001])).

tff(c_3117,plain,(
    ! [A_613,B_614,C_615] :
      ( k3_funct_2(u1_struct_0(A_613),B_614,C_615,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1(C_615,'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
      | ~ m1_subset_1(C_615,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613),B_614)))
      | ~ v1_funct_2(C_615,u1_struct_0(A_613),B_614)
      | ~ v1_funct_1(C_615)
      | v1_xboole_0(u1_struct_0(A_613))
      | ~ m1_pre_topc('#skF_3',A_613)
      | ~ l1_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_3007,c_4])).

tff(c_3126,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_3117])).

tff(c_3131,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_250,c_50,c_48,c_2939,c_3126])).

tff(c_3132,plain,
    ( k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3131])).

tff(c_3133,plain,(
    k3_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4','#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) = '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_3116,c_3132])).

tff(c_3136,plain,
    ( k1_funct_1(k4_tmap_1('#skF_2','#skF_3'),'#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')) != '#skF_1'('#skF_3','#skF_2','#skF_3',k4_tmap_1('#skF_2','#skF_3'),'#skF_4')
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
    inference(superposition,[status(thm),theory(equality)],[c_3133,c_34])).

tff(c_3140,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),'#skF_4',k4_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_84,c_73,c_250,c_50,c_48,c_46,c_2717,c_2730,c_2557,c_3038,c_3136])).

tff(c_3141,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_54,c_2760,c_3140])).

tff(c_3145,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3141])).

tff(c_3148,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_3145])).

tff(c_3150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3148])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.44/2.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.59  
% 7.59/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.59/2.59  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.59/2.59  
% 7.59/2.59  %Foreground sorts:
% 7.59/2.59  
% 7.59/2.59  
% 7.59/2.59  %Background operators:
% 7.59/2.59  
% 7.59/2.59  
% 7.59/2.59  %Foreground operators:
% 7.59/2.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.59/2.59  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 7.59/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.59/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.59/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.59/2.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.59/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.59/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.59/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.59/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.59/2.59  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.59/2.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.59/2.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 7.59/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.59/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.59/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.59/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.59/2.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.59/2.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.59/2.59  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.59/2.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.59/2.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.59/2.59  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 7.59/2.59  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.59/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.59/2.59  
% 7.80/2.63  tff(f_235, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 7.80/2.63  tff(f_130, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 7.80/2.63  tff(f_61, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.80/2.63  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.80/2.63  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.80/2.63  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.80/2.63  tff(f_185, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 7.80/2.63  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.80/2.63  tff(f_115, axiom, (![A, B, C, D]: ((((((l1_struct_0(A) & l1_struct_0(B)) & v1_funct_1(C)) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) & l1_struct_0(D)) => ((v1_funct_1(k2_tmap_1(A, B, C, D)) & v1_funct_2(k2_tmap_1(A, B, C, D), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k2_tmap_1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 7.80/2.63  tff(f_97, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 7.80/2.63  tff(f_205, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 7.80/2.63  tff(f_45, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 7.80/2.63  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.80/2.63  tff(f_32, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 7.80/2.63  tff(c_60, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_52, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_24, plain, (![A_30, B_31]: (m1_subset_1(k4_tmap_1(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_31), u1_struct_0(A_30)))) | ~m1_pre_topc(B_31, A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.80/2.63  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_48, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_99, plain, (![A_139, B_140, D_141]: (r2_funct_2(A_139, B_140, D_141, D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))) | ~v1_funct_2(D_141, A_139, B_140) | ~v1_funct_1(D_141))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.80/2.63  tff(c_101, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_99])).
% 7.80/2.63  tff(c_104, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_101])).
% 7.80/2.63  tff(c_28, plain, (![A_30, B_31]: (v1_funct_1(k4_tmap_1(A_30, B_31)) | ~m1_pre_topc(B_31, A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.80/2.63  tff(c_74, plain, (![B_121, A_122]: (v2_pre_topc(B_121) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.80/2.63  tff(c_80, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_74])).
% 7.80/2.63  tff(c_84, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_80])).
% 7.80/2.63  tff(c_63, plain, (![B_119, A_120]: (l1_pre_topc(B_119) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.80/2.63  tff(c_69, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_63])).
% 7.80/2.63  tff(c_73, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_69])).
% 7.80/2.63  tff(c_32, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.80/2.63  tff(c_206, plain, (![A_190, B_189, D_193, C_191, E_192]: (m1_subset_1('#skF_1'(B_189, A_190, C_191, E_192, D_193), u1_struct_0(B_189)) | r2_funct_2(u1_struct_0(C_191), u1_struct_0(A_190), k2_tmap_1(B_189, A_190, D_193, C_191), E_192) | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_191), u1_struct_0(A_190)))) | ~v1_funct_2(E_192, u1_struct_0(C_191), u1_struct_0(A_190)) | ~v1_funct_1(E_192) | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_189), u1_struct_0(A_190)))) | ~v1_funct_2(D_193, u1_struct_0(B_189), u1_struct_0(A_190)) | ~v1_funct_1(D_193) | ~m1_pre_topc(C_191, B_189) | v2_struct_0(C_191) | ~l1_pre_topc(B_189) | ~v2_pre_topc(B_189) | v2_struct_0(B_189) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_185])).
% 7.80/2.63  tff(c_212, plain, (![B_189, D_193]: (m1_subset_1('#skF_1'(B_189, '#skF_2', '#skF_3', '#skF_4', D_193), u1_struct_0(B_189)) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1(B_189, '#skF_2', D_193, '#skF_3'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_189), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_193, u1_struct_0(B_189), u1_struct_0('#skF_2')) | ~v1_funct_1(D_193) | ~m1_pre_topc('#skF_3', B_189) | v2_struct_0('#skF_3') | ~l1_pre_topc(B_189) | ~v2_pre_topc(B_189) | v2_struct_0(B_189) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_206])).
% 7.80/2.63  tff(c_217, plain, (![B_189, D_193]: (m1_subset_1('#skF_1'(B_189, '#skF_2', '#skF_3', '#skF_4', D_193), u1_struct_0(B_189)) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1(B_189, '#skF_2', D_193, '#skF_3'), '#skF_4') | ~m1_subset_1(D_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_189), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_193, u1_struct_0(B_189), u1_struct_0('#skF_2')) | ~v1_funct_1(D_193) | ~m1_pre_topc('#skF_3', B_189) | v2_struct_0('#skF_3') | ~l1_pre_topc(B_189) | ~v2_pre_topc(B_189) | v2_struct_0(B_189) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_48, c_212])).
% 7.80/2.63  tff(c_221, plain, (![B_201, D_202]: (m1_subset_1('#skF_1'(B_201, '#skF_2', '#skF_3', '#skF_4', D_202), u1_struct_0(B_201)) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1(B_201, '#skF_2', D_202, '#skF_3'), '#skF_4') | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_201), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_202, u1_struct_0(B_201), u1_struct_0('#skF_2')) | ~v1_funct_1(D_202) | ~m1_pre_topc('#skF_3', B_201) | ~l1_pre_topc(B_201) | ~v2_pre_topc(B_201) | v2_struct_0(B_201))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_217])).
% 7.80/2.63  tff(c_229, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_221])).
% 7.80/2.63  tff(c_239, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_73, c_50, c_48, c_229])).
% 7.80/2.63  tff(c_240, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_239])).
% 7.80/2.63  tff(c_241, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_240])).
% 7.80/2.63  tff(c_244, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_241])).
% 7.80/2.63  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_244])).
% 7.80/2.63  tff(c_250, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_240])).
% 7.80/2.63  tff(c_12, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.80/2.63  tff(c_124, plain, (![A_154, B_155, C_156, D_157]: (v1_funct_1(k2_tmap_1(A_154, B_155, C_156, D_157)) | ~l1_struct_0(D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_154), u1_struct_0(B_155)))) | ~v1_funct_2(C_156, u1_struct_0(A_154), u1_struct_0(B_155)) | ~v1_funct_1(C_156) | ~l1_struct_0(B_155) | ~l1_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.80/2.63  tff(c_128, plain, (![D_157]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_157)) | ~l1_struct_0(D_157) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_124])).
% 7.80/2.63  tff(c_132, plain, (![D_157]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_157)) | ~l1_struct_0(D_157) | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_128])).
% 7.80/2.63  tff(c_133, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_132])).
% 7.80/2.63  tff(c_136, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_133])).
% 7.80/2.63  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_136])).
% 7.80/2.63  tff(c_142, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_132])).
% 7.80/2.63  tff(c_141, plain, (![D_157]: (~l1_struct_0('#skF_2') | v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_157)) | ~l1_struct_0(D_157))), inference(splitRight, [status(thm)], [c_132])).
% 7.80/2.63  tff(c_143, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_141])).
% 7.80/2.63  tff(c_153, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12, c_143])).
% 7.80/2.63  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_153])).
% 7.80/2.63  tff(c_159, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_141])).
% 7.80/2.63  tff(c_169, plain, (![A_167, B_168, C_169, D_170]: (v1_funct_2(k2_tmap_1(A_167, B_168, C_169, D_170), u1_struct_0(D_170), u1_struct_0(B_168)) | ~l1_struct_0(D_170) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_167), u1_struct_0(B_168)))) | ~v1_funct_2(C_169, u1_struct_0(A_167), u1_struct_0(B_168)) | ~v1_funct_1(C_169) | ~l1_struct_0(B_168) | ~l1_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.80/2.63  tff(c_173, plain, (![D_170]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_170), u1_struct_0(D_170), u1_struct_0('#skF_2')) | ~l1_struct_0(D_170) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_169])).
% 7.80/2.63  tff(c_177, plain, (![D_170]: (v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_170), u1_struct_0(D_170), u1_struct_0('#skF_2')) | ~l1_struct_0(D_170))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_159, c_50, c_48, c_173])).
% 7.80/2.63  tff(c_18, plain, (![A_26, B_27, C_28, D_29]: (m1_subset_1(k2_tmap_1(A_26, B_27, C_28, D_29), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_29), u1_struct_0(B_27)))) | ~l1_struct_0(D_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_26), u1_struct_0(B_27)))) | ~v1_funct_2(C_28, u1_struct_0(A_26), u1_struct_0(B_27)) | ~v1_funct_1(C_28) | ~l1_struct_0(B_27) | ~l1_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.80/2.63  tff(c_158, plain, (![D_157]: (v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', D_157)) | ~l1_struct_0(D_157))), inference(splitRight, [status(thm)], [c_141])).
% 7.80/2.63  tff(c_251, plain, (![E_206, B_203, D_207, C_205, A_204]: (r2_hidden('#skF_1'(B_203, A_204, C_205, E_206, D_207), u1_struct_0(C_205)) | r2_funct_2(u1_struct_0(C_205), u1_struct_0(A_204), k2_tmap_1(B_203, A_204, D_207, C_205), E_206) | ~m1_subset_1(E_206, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_205), u1_struct_0(A_204)))) | ~v1_funct_2(E_206, u1_struct_0(C_205), u1_struct_0(A_204)) | ~v1_funct_1(E_206) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_203), u1_struct_0(A_204)))) | ~v1_funct_2(D_207, u1_struct_0(B_203), u1_struct_0(A_204)) | ~v1_funct_1(D_207) | ~m1_pre_topc(C_205, B_203) | v2_struct_0(C_205) | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_185])).
% 7.80/2.63  tff(c_257, plain, (![B_203, D_207]: (r2_hidden('#skF_1'(B_203, '#skF_2', '#skF_3', '#skF_4', D_207), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1(B_203, '#skF_2', D_207, '#skF_3'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_203), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_207, u1_struct_0(B_203), u1_struct_0('#skF_2')) | ~v1_funct_1(D_207) | ~m1_pre_topc('#skF_3', B_203) | v2_struct_0('#skF_3') | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_251])).
% 7.80/2.63  tff(c_262, plain, (![B_203, D_207]: (r2_hidden('#skF_1'(B_203, '#skF_2', '#skF_3', '#skF_4', D_207), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1(B_203, '#skF_2', D_207, '#skF_3'), '#skF_4') | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_203), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_207, u1_struct_0(B_203), u1_struct_0('#skF_2')) | ~v1_funct_1(D_207) | ~m1_pre_topc('#skF_3', B_203) | v2_struct_0('#skF_3') | ~l1_pre_topc(B_203) | ~v2_pre_topc(B_203) | v2_struct_0(B_203) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_50, c_48, c_257])).
% 7.80/2.63  tff(c_1350, plain, (![B_357, D_358]: (r2_hidden('#skF_1'(B_357, '#skF_2', '#skF_3', '#skF_4', D_358), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1(B_357, '#skF_2', D_358, '#skF_3'), '#skF_4') | ~m1_subset_1(D_358, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_357), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_358, u1_struct_0(B_357), u1_struct_0('#skF_2')) | ~v1_funct_1(D_358) | ~m1_pre_topc('#skF_3', B_357) | ~l1_pre_topc(B_357) | ~v2_pre_topc(B_357) | v2_struct_0(B_357))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_262])).
% 7.80/2.63  tff(c_1361, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1350])).
% 7.80/2.63  tff(c_1371, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_73, c_250, c_50, c_48, c_1361])).
% 7.80/2.63  tff(c_1372, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_1371])).
% 7.80/2.63  tff(c_1373, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1372])).
% 7.80/2.63  tff(c_8, plain, (![D_11, C_10, A_8, B_9]: (D_11=C_10 | ~r2_funct_2(A_8, B_9, C_10, D_11) | ~m1_subset_1(D_11, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(D_11, A_8, B_9) | ~v1_funct_1(D_11) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(C_10, A_8, B_9) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.80/2.63  tff(c_1375, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1373, c_8])).
% 7.80/2.63  tff(c_1378, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1375])).
% 7.80/2.63  tff(c_1402, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1378])).
% 7.80/2.63  tff(c_1412, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_158, c_1402])).
% 7.80/2.63  tff(c_1416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1412])).
% 7.80/2.63  tff(c_1417, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1378])).
% 7.80/2.63  tff(c_1419, plain, (~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1417])).
% 7.80/2.63  tff(c_1428, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1419])).
% 7.80/2.63  tff(c_1432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_159, c_50, c_48, c_46, c_1428])).
% 7.80/2.63  tff(c_1433, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1417])).
% 7.80/2.63  tff(c_1488, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1433])).
% 7.80/2.63  tff(c_1491, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_177, c_1488])).
% 7.80/2.63  tff(c_1495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_1491])).
% 7.80/2.63  tff(c_1496, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1433])).
% 7.80/2.63  tff(c_2071, plain, (![B_482, A_483, B_484, D_485]: (r2_hidden('#skF_1'(B_482, A_483, B_484, k4_tmap_1(A_483, B_484), D_485), u1_struct_0(B_484)) | r2_funct_2(u1_struct_0(B_484), u1_struct_0(A_483), k2_tmap_1(B_482, A_483, D_485, B_484), k4_tmap_1(A_483, B_484)) | ~v1_funct_2(k4_tmap_1(A_483, B_484), u1_struct_0(B_484), u1_struct_0(A_483)) | ~v1_funct_1(k4_tmap_1(A_483, B_484)) | ~m1_subset_1(D_485, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_482), u1_struct_0(A_483)))) | ~v1_funct_2(D_485, u1_struct_0(B_482), u1_struct_0(A_483)) | ~v1_funct_1(D_485) | ~m1_pre_topc(B_484, B_482) | v2_struct_0(B_484) | ~l1_pre_topc(B_482) | ~v2_pre_topc(B_482) | v2_struct_0(B_482) | ~m1_pre_topc(B_484, A_483) | ~l1_pre_topc(A_483) | ~v2_pre_topc(A_483) | v2_struct_0(A_483))), inference(resolution, [status(thm)], [c_24, c_251])).
% 7.80/2.63  tff(c_2076, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_2071])).
% 7.80/2.63  tff(c_2079, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_2076])).
% 7.80/2.63  tff(c_2080, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2079])).
% 7.80/2.63  tff(c_2081, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2080])).
% 7.80/2.63  tff(c_2084, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_2081])).
% 7.80/2.63  tff(c_2087, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2084])).
% 7.80/2.63  tff(c_2089, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2087])).
% 7.80/2.63  tff(c_2091, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2080])).
% 7.80/2.63  tff(c_26, plain, (![A_30, B_31]: (v1_funct_2(k4_tmap_1(A_30, B_31), u1_struct_0(B_31), u1_struct_0(A_30)) | ~m1_pre_topc(B_31, A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.80/2.63  tff(c_2090, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2080])).
% 7.80/2.63  tff(c_2094, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2090])).
% 7.80/2.63  tff(c_2097, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2094])).
% 7.80/2.63  tff(c_2100, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2097])).
% 7.80/2.63  tff(c_2102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2100])).
% 7.80/2.63  tff(c_2104, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2090])).
% 7.80/2.63  tff(c_2103, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2090])).
% 7.80/2.63  tff(c_2105, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2103])).
% 7.80/2.63  tff(c_2107, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2105, c_8])).
% 7.80/2.63  tff(c_2110, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_2091, c_2104, c_2107])).
% 7.80/2.63  tff(c_2112, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2110])).
% 7.80/2.63  tff(c_2115, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2112])).
% 7.80/2.63  tff(c_2118, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2115])).
% 7.80/2.63  tff(c_2120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2118])).
% 7.80/2.63  tff(c_2121, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2110])).
% 7.80/2.63  tff(c_42, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_2126, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2121, c_42])).
% 7.80/2.63  tff(c_2132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_2126])).
% 7.80/2.63  tff(c_2134, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2103])).
% 7.80/2.63  tff(c_2159, plain, (![B_495, A_496, B_497, D_498]: (m1_subset_1('#skF_1'(B_495, A_496, B_497, k4_tmap_1(A_496, B_497), D_498), u1_struct_0(B_495)) | r2_funct_2(u1_struct_0(B_497), u1_struct_0(A_496), k2_tmap_1(B_495, A_496, D_498, B_497), k4_tmap_1(A_496, B_497)) | ~v1_funct_2(k4_tmap_1(A_496, B_497), u1_struct_0(B_497), u1_struct_0(A_496)) | ~v1_funct_1(k4_tmap_1(A_496, B_497)) | ~m1_subset_1(D_498, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_495), u1_struct_0(A_496)))) | ~v1_funct_2(D_498, u1_struct_0(B_495), u1_struct_0(A_496)) | ~v1_funct_1(D_498) | ~m1_pre_topc(B_497, B_495) | v2_struct_0(B_497) | ~l1_pre_topc(B_495) | ~v2_pre_topc(B_495) | v2_struct_0(B_495) | ~m1_pre_topc(B_497, A_496) | ~l1_pre_topc(A_496) | ~v2_pre_topc(A_496) | v2_struct_0(A_496))), inference(resolution, [status(thm)], [c_24, c_206])).
% 7.80/2.63  tff(c_2168, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_2159])).
% 7.80/2.63  tff(c_2173, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_2091, c_2104, c_2168])).
% 7.80/2.63  tff(c_2174, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2134, c_2173])).
% 7.80/2.63  tff(c_16, plain, (![C_25, A_19, B_23]: (m1_subset_1(C_25, u1_struct_0(A_19)) | ~m1_subset_1(C_25, u1_struct_0(B_23)) | ~m1_pre_topc(B_23, A_19) | v2_struct_0(B_23) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.80/2.63  tff(c_2178, plain, (![A_19]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_19)) | ~m1_pre_topc('#skF_3', A_19) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(resolution, [status(thm)], [c_2174, c_16])).
% 7.80/2.63  tff(c_2190, plain, (![A_499]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_499)) | ~m1_pre_topc('#skF_3', A_499) | ~l1_pre_topc(A_499) | v2_struct_0(A_499))), inference(negUnitSimplification, [status(thm)], [c_54, c_2178])).
% 7.80/2.63  tff(c_2133, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2103])).
% 7.80/2.63  tff(c_44, plain, (![D_116]: (k1_funct_1('#skF_4', D_116)=D_116 | ~r2_hidden(D_116, u1_struct_0('#skF_3')) | ~m1_subset_1(D_116, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 7.80/2.63  tff(c_2156, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2133, c_44])).
% 7.80/2.63  tff(c_2157, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2156])).
% 7.80/2.63  tff(c_2193, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2190, c_2157])).
% 7.80/2.63  tff(c_2200, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2193])).
% 7.80/2.63  tff(c_2202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2200])).
% 7.80/2.63  tff(c_2204, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2156])).
% 7.80/2.63  tff(c_40, plain, (![A_98, B_102, C_104]: (k1_funct_1(k4_tmap_1(A_98, B_102), C_104)=C_104 | ~r2_hidden(C_104, u1_struct_0(B_102)) | ~m1_subset_1(C_104, u1_struct_0(A_98)) | ~m1_pre_topc(B_102, A_98) | v2_struct_0(B_102) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.80/2.63  tff(c_2149, plain, (![A_98]: (k1_funct_1(k4_tmap_1(A_98, '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_98)) | ~m1_pre_topc('#skF_3', A_98) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_2133, c_40])).
% 7.80/2.63  tff(c_2282, plain, (![A_508]: (k1_funct_1(k4_tmap_1(A_508, '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_508)) | ~m1_pre_topc('#skF_3', A_508) | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(negUnitSimplification, [status(thm)], [c_54, c_2149])).
% 7.80/2.63  tff(c_2296, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2204, c_2282])).
% 7.80/2.63  tff(c_2305, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2296])).
% 7.80/2.63  tff(c_2306, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_2305])).
% 7.80/2.63  tff(c_2203, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_2156])).
% 7.80/2.63  tff(c_788, plain, (![B_282, D_283]: (r2_hidden('#skF_1'(B_282, '#skF_2', '#skF_3', '#skF_4', D_283), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1(B_282, '#skF_2', D_283, '#skF_3'), '#skF_4') | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_282), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_283, u1_struct_0(B_282), u1_struct_0('#skF_2')) | ~v1_funct_1(D_283) | ~m1_pre_topc('#skF_3', B_282) | ~l1_pre_topc(B_282) | ~v2_pre_topc(B_282) | v2_struct_0(B_282))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_262])).
% 7.80/2.63  tff(c_799, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_788])).
% 7.80/2.63  tff(c_809, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_73, c_250, c_50, c_48, c_799])).
% 7.80/2.63  tff(c_810, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_809])).
% 7.80/2.63  tff(c_811, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_810])).
% 7.80/2.63  tff(c_813, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_811, c_8])).
% 7.80/2.63  tff(c_816, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_813])).
% 7.80/2.63  tff(c_817, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_816])).
% 7.80/2.63  tff(c_826, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_158, c_817])).
% 7.80/2.63  tff(c_830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_826])).
% 7.80/2.63  tff(c_831, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_816])).
% 7.80/2.63  tff(c_833, plain, (~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_831])).
% 7.80/2.63  tff(c_836, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_833])).
% 7.80/2.63  tff(c_840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_159, c_50, c_48, c_46, c_836])).
% 7.80/2.63  tff(c_841, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_831])).
% 7.80/2.63  tff(c_899, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_841])).
% 7.80/2.63  tff(c_902, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_177, c_899])).
% 7.80/2.63  tff(c_906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_902])).
% 7.80/2.63  tff(c_907, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_841])).
% 7.80/2.63  tff(c_1051, plain, (![B_316, A_317, B_318, D_319]: (m1_subset_1('#skF_1'(B_316, A_317, B_318, k4_tmap_1(A_317, B_318), D_319), u1_struct_0(B_316)) | r2_funct_2(u1_struct_0(B_318), u1_struct_0(A_317), k2_tmap_1(B_316, A_317, D_319, B_318), k4_tmap_1(A_317, B_318)) | ~v1_funct_2(k4_tmap_1(A_317, B_318), u1_struct_0(B_318), u1_struct_0(A_317)) | ~v1_funct_1(k4_tmap_1(A_317, B_318)) | ~m1_subset_1(D_319, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_316), u1_struct_0(A_317)))) | ~v1_funct_2(D_319, u1_struct_0(B_316), u1_struct_0(A_317)) | ~v1_funct_1(D_319) | ~m1_pre_topc(B_318, B_316) | v2_struct_0(B_318) | ~l1_pre_topc(B_316) | ~v2_pre_topc(B_316) | v2_struct_0(B_316) | ~m1_pre_topc(B_318, A_317) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317) | v2_struct_0(A_317))), inference(resolution, [status(thm)], [c_24, c_206])).
% 7.80/2.63  tff(c_1060, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_907, c_1051])).
% 7.80/2.63  tff(c_1065, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_1060])).
% 7.80/2.63  tff(c_1066, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1065])).
% 7.80/2.63  tff(c_1067, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1066])).
% 7.80/2.63  tff(c_1070, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_1067])).
% 7.80/2.63  tff(c_1073, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_1070])).
% 7.80/2.63  tff(c_1075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1073])).
% 7.80/2.63  tff(c_1077, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1066])).
% 7.80/2.63  tff(c_1076, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1066])).
% 7.80/2.63  tff(c_1080, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1076])).
% 7.80/2.63  tff(c_1083, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_1080])).
% 7.80/2.63  tff(c_1086, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_1083])).
% 7.80/2.63  tff(c_1088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1086])).
% 7.80/2.63  tff(c_1090, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1076])).
% 7.80/2.63  tff(c_1089, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1076])).
% 7.80/2.63  tff(c_1091, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1089])).
% 7.80/2.63  tff(c_1093, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1091, c_8])).
% 7.80/2.63  tff(c_1096, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1077, c_1090, c_1093])).
% 7.80/2.63  tff(c_1107, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1096])).
% 7.80/2.63  tff(c_1110, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1107])).
% 7.80/2.63  tff(c_1113, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_1110])).
% 7.80/2.63  tff(c_1115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1113])).
% 7.80/2.63  tff(c_1116, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1096])).
% 7.80/2.63  tff(c_1121, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_42])).
% 7.80/2.63  tff(c_1127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1121])).
% 7.80/2.63  tff(c_1129, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1089])).
% 7.80/2.63  tff(c_1312, plain, (![B_353, A_354, B_355, D_356]: (r2_hidden('#skF_1'(B_353, A_354, B_355, k4_tmap_1(A_354, B_355), D_356), u1_struct_0(B_355)) | r2_funct_2(u1_struct_0(B_355), u1_struct_0(A_354), k2_tmap_1(B_353, A_354, D_356, B_355), k4_tmap_1(A_354, B_355)) | ~v1_funct_2(k4_tmap_1(A_354, B_355), u1_struct_0(B_355), u1_struct_0(A_354)) | ~v1_funct_1(k4_tmap_1(A_354, B_355)) | ~m1_subset_1(D_356, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_353), u1_struct_0(A_354)))) | ~v1_funct_2(D_356, u1_struct_0(B_353), u1_struct_0(A_354)) | ~v1_funct_1(D_356) | ~m1_pre_topc(B_355, B_353) | v2_struct_0(B_355) | ~l1_pre_topc(B_353) | ~v2_pre_topc(B_353) | v2_struct_0(B_353) | ~m1_pre_topc(B_355, A_354) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354) | v2_struct_0(A_354))), inference(resolution, [status(thm)], [c_24, c_251])).
% 7.80/2.63  tff(c_1317, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_907, c_1312])).
% 7.80/2.63  tff(c_1320, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_1077, c_1090, c_1317])).
% 7.80/2.63  tff(c_1321, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_1129, c_1320])).
% 7.80/2.63  tff(c_249, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_240])).
% 7.80/2.63  tff(c_276, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_249])).
% 7.80/2.63  tff(c_4, plain, (![A_4, B_5, C_6, D_7]: (k3_funct_2(A_4, B_5, C_6, D_7)=k1_funct_1(C_6, D_7) | ~m1_subset_1(D_7, A_4) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))) | ~v1_funct_2(C_6, A_4, B_5) | ~v1_funct_1(C_6) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.80/2.63  tff(c_281, plain, (![B_5, C_6]: (k3_funct_2(u1_struct_0('#skF_3'), B_5, C_6, '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'))=k1_funct_1(C_6, '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4')) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_5))) | ~v1_funct_2(C_6, u1_struct_0('#skF_3'), B_5) | ~v1_funct_1(C_6) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_276, c_4])).
% 7.80/2.63  tff(c_339, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_281])).
% 7.80/2.63  tff(c_90, plain, (![B_126, A_127]: (m1_subset_1(u1_struct_0(B_126), k1_zfmisc_1(u1_struct_0(A_127))) | ~m1_pre_topc(B_126, A_127) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_137])).
% 7.80/2.63  tff(c_2, plain, (![C_3, B_2, A_1]: (~v1_xboole_0(C_3) | ~m1_subset_1(B_2, k1_zfmisc_1(C_3)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.80/2.63  tff(c_93, plain, (![A_127, A_1, B_126]: (~v1_xboole_0(u1_struct_0(A_127)) | ~r2_hidden(A_1, u1_struct_0(B_126)) | ~m1_pre_topc(B_126, A_127) | ~l1_pre_topc(A_127))), inference(resolution, [status(thm)], [c_90, c_2])).
% 7.80/2.63  tff(c_342, plain, (![A_1, B_126]: (~r2_hidden(A_1, u1_struct_0(B_126)) | ~m1_pre_topc(B_126, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_339, c_93])).
% 7.80/2.63  tff(c_345, plain, (![A_1, B_126]: (~r2_hidden(A_1, u1_struct_0(B_126)) | ~m1_pre_topc(B_126, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_342])).
% 7.80/2.63  tff(c_1324, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1321, c_345])).
% 7.80/2.63  tff(c_1333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_1324])).
% 7.80/2.63  tff(c_1334, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_810])).
% 7.80/2.63  tff(c_1338, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1334, c_345])).
% 7.80/2.63  tff(c_1347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_1338])).
% 7.80/2.63  tff(c_1349, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_281])).
% 7.80/2.63  tff(c_2248, plain, (![B_503, A_504, B_505, D_506]: (m1_subset_1('#skF_1'(B_503, A_504, B_505, k4_tmap_1(A_504, B_505), D_506), u1_struct_0(B_503)) | r2_funct_2(u1_struct_0(B_505), u1_struct_0(A_504), k2_tmap_1(B_503, A_504, D_506, B_505), k4_tmap_1(A_504, B_505)) | ~v1_funct_2(k4_tmap_1(A_504, B_505), u1_struct_0(B_505), u1_struct_0(A_504)) | ~v1_funct_1(k4_tmap_1(A_504, B_505)) | ~m1_subset_1(D_506, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_503), u1_struct_0(A_504)))) | ~v1_funct_2(D_506, u1_struct_0(B_503), u1_struct_0(A_504)) | ~v1_funct_1(D_506) | ~m1_pre_topc(B_505, B_503) | v2_struct_0(B_505) | ~l1_pre_topc(B_503) | ~v2_pre_topc(B_503) | v2_struct_0(B_503) | ~m1_pre_topc(B_505, A_504) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(resolution, [status(thm)], [c_24, c_206])).
% 7.80/2.63  tff(c_2257, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1496, c_2248])).
% 7.80/2.63  tff(c_2262, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_2091, c_2104, c_2257])).
% 7.80/2.63  tff(c_2263, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2134, c_2262])).
% 7.80/2.63  tff(c_2265, plain, (![B_5, C_6]: (k3_funct_2(u1_struct_0('#skF_3'), B_5, C_6, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(C_6, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_5))) | ~v1_funct_2(C_6, u1_struct_0('#skF_3'), B_5) | ~v1_funct_1(C_6) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2263, c_4])).
% 7.80/2.63  tff(c_2369, plain, (![B_518, C_519]: (k3_funct_2(u1_struct_0('#skF_3'), B_518, C_519, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(C_519, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~m1_subset_1(C_519, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_518))) | ~v1_funct_2(C_519, u1_struct_0('#skF_3'), B_518) | ~v1_funct_1(C_519))), inference(negUnitSimplification, [status(thm)], [c_1349, c_2265])).
% 7.80/2.63  tff(c_2380, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2369])).
% 7.80/2.63  tff(c_2387, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2203, c_2380])).
% 7.80/2.63  tff(c_34, plain, (![D_92, A_36, C_84, B_68, E_96]: (k3_funct_2(u1_struct_0(B_68), u1_struct_0(A_36), D_92, '#skF_1'(B_68, A_36, C_84, E_96, D_92))!=k1_funct_1(E_96, '#skF_1'(B_68, A_36, C_84, E_96, D_92)) | r2_funct_2(u1_struct_0(C_84), u1_struct_0(A_36), k2_tmap_1(B_68, A_36, D_92, C_84), E_96) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_84), u1_struct_0(A_36)))) | ~v1_funct_2(E_96, u1_struct_0(C_84), u1_struct_0(A_36)) | ~v1_funct_1(E_96) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_68), u1_struct_0(A_36)))) | ~v1_funct_2(D_92, u1_struct_0(B_68), u1_struct_0(A_36)) | ~v1_funct_1(D_92) | ~m1_pre_topc(C_84, B_68) | v2_struct_0(C_84) | ~l1_pre_topc(B_68) | ~v2_pre_topc(B_68) | v2_struct_0(B_68) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_185])).
% 7.80/2.63  tff(c_2390, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2387, c_34])).
% 7.80/2.63  tff(c_2394, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_84, c_73, c_250, c_50, c_48, c_46, c_2091, c_2104, c_1496, c_2306, c_2390])).
% 7.80/2.63  tff(c_2395, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2134, c_2394])).
% 7.80/2.63  tff(c_2399, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2395])).
% 7.80/2.63  tff(c_2402, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2399])).
% 7.80/2.63  tff(c_2404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2402])).
% 7.80/2.63  tff(c_2406, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_1372])).
% 7.80/2.63  tff(c_280, plain, (![A_19]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0(A_19)) | ~m1_pre_topc('#skF_3', A_19) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(resolution, [status(thm)], [c_276, c_16])).
% 7.80/2.63  tff(c_285, plain, (![A_208]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0(A_208)) | ~m1_pre_topc('#skF_3', A_208) | ~l1_pre_topc(A_208) | v2_struct_0(A_208))), inference(negUnitSimplification, [status(thm)], [c_54, c_280])).
% 7.80/2.63  tff(c_292, plain, (![A_209, A_210]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0(A_209)) | ~m1_pre_topc(A_210, A_209) | ~l1_pre_topc(A_209) | v2_struct_0(A_209) | ~m1_pre_topc('#skF_3', A_210) | ~l1_pre_topc(A_210) | v2_struct_0(A_210))), inference(resolution, [status(thm)], [c_285, c_16])).
% 7.80/2.63  tff(c_298, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_292])).
% 7.80/2.63  tff(c_306, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_2') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_250, c_56, c_298])).
% 7.80/2.63  tff(c_307, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_60, c_306])).
% 7.80/2.63  tff(c_2405, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1372])).
% 7.80/2.63  tff(c_2417, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2405, c_44])).
% 7.80/2.63  tff(c_2423, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_2417])).
% 7.80/2.63  tff(c_2428, plain, (![B_521, C_522]: (k3_funct_2(u1_struct_0('#skF_3'), B_521, C_522, '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'))=k1_funct_1(C_522, '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4')) | ~m1_subset_1(C_522, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_521))) | ~v1_funct_2(C_522, u1_struct_0('#skF_3'), B_521) | ~v1_funct_1(C_522))), inference(splitRight, [status(thm)], [c_281])).
% 7.80/2.63  tff(c_2439, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2428])).
% 7.80/2.63  tff(c_2446, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_2423, c_2439])).
% 7.80/2.63  tff(c_2451, plain, (![D_527, C_525, E_526, B_523, A_524]: (k3_funct_2(u1_struct_0(B_523), u1_struct_0(A_524), D_527, '#skF_1'(B_523, A_524, C_525, E_526, D_527))!=k1_funct_1(E_526, '#skF_1'(B_523, A_524, C_525, E_526, D_527)) | r2_funct_2(u1_struct_0(C_525), u1_struct_0(A_524), k2_tmap_1(B_523, A_524, D_527, C_525), E_526) | ~m1_subset_1(E_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_525), u1_struct_0(A_524)))) | ~v1_funct_2(E_526, u1_struct_0(C_525), u1_struct_0(A_524)) | ~v1_funct_1(E_526) | ~m1_subset_1(D_527, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_523), u1_struct_0(A_524)))) | ~v1_funct_2(D_527, u1_struct_0(B_523), u1_struct_0(A_524)) | ~v1_funct_1(D_527) | ~m1_pre_topc(C_525, B_523) | v2_struct_0(C_525) | ~l1_pre_topc(B_523) | ~v2_pre_topc(B_523) | v2_struct_0(B_523) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(cnfTransformation, [status(thm)], [f_185])).
% 7.80/2.63  tff(c_2453, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4'))!='#skF_1'('#skF_3', '#skF_2', '#skF_3', '#skF_4', '#skF_4') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2446, c_2451])).
% 7.80/2.63  tff(c_2455, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_84, c_73, c_250, c_50, c_48, c_46, c_50, c_48, c_46, c_2423, c_2453])).
% 7.80/2.63  tff(c_2457, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2406, c_2455])).
% 7.80/2.63  tff(c_2458, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_249])).
% 7.80/2.63  tff(c_2461, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2458, c_8])).
% 7.80/2.63  tff(c_2464, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_2461])).
% 7.80/2.63  tff(c_2465, plain, (~v1_funct_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2464])).
% 7.80/2.63  tff(c_2491, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_158, c_2465])).
% 7.80/2.63  tff(c_2495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_2491])).
% 7.80/2.63  tff(c_2496, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2464])).
% 7.80/2.63  tff(c_2498, plain, (~m1_subset_1(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2496])).
% 7.80/2.63  tff(c_2501, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2498])).
% 7.80/2.63  tff(c_2505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_159, c_50, c_48, c_46, c_2501])).
% 7.80/2.63  tff(c_2506, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2496])).
% 7.80/2.63  tff(c_2549, plain, (~v1_funct_2(k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2506])).
% 7.80/2.63  tff(c_2552, plain, (~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_177, c_2549])).
% 7.80/2.63  tff(c_2556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_2552])).
% 7.80/2.63  tff(c_2557, plain, (k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2506])).
% 7.80/2.63  tff(c_2697, plain, (![B_565, A_566, B_567, D_568]: (r2_hidden('#skF_1'(B_565, A_566, B_567, k4_tmap_1(A_566, B_567), D_568), u1_struct_0(B_567)) | r2_funct_2(u1_struct_0(B_567), u1_struct_0(A_566), k2_tmap_1(B_565, A_566, D_568, B_567), k4_tmap_1(A_566, B_567)) | ~v1_funct_2(k4_tmap_1(A_566, B_567), u1_struct_0(B_567), u1_struct_0(A_566)) | ~v1_funct_1(k4_tmap_1(A_566, B_567)) | ~m1_subset_1(D_568, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_565), u1_struct_0(A_566)))) | ~v1_funct_2(D_568, u1_struct_0(B_565), u1_struct_0(A_566)) | ~v1_funct_1(D_568) | ~m1_pre_topc(B_567, B_565) | v2_struct_0(B_567) | ~l1_pre_topc(B_565) | ~v2_pre_topc(B_565) | v2_struct_0(B_565) | ~m1_pre_topc(B_567, A_566) | ~l1_pre_topc(A_566) | ~v2_pre_topc(A_566) | v2_struct_0(A_566))), inference(resolution, [status(thm)], [c_24, c_251])).
% 7.80/2.63  tff(c_2702, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2557, c_2697])).
% 7.80/2.63  tff(c_2705, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_2702])).
% 7.80/2.63  tff(c_2706, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2705])).
% 7.80/2.63  tff(c_2707, plain, (~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2706])).
% 7.80/2.63  tff(c_2710, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_2707])).
% 7.80/2.63  tff(c_2713, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2710])).
% 7.80/2.63  tff(c_2715, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2713])).
% 7.80/2.63  tff(c_2717, plain, (v1_funct_1(k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2706])).
% 7.80/2.63  tff(c_2716, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2706])).
% 7.80/2.63  tff(c_2720, plain, (~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2716])).
% 7.80/2.63  tff(c_2723, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2720])).
% 7.80/2.63  tff(c_2726, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2723])).
% 7.80/2.63  tff(c_2728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2726])).
% 7.80/2.63  tff(c_2730, plain, (v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2716])).
% 7.80/2.63  tff(c_2729, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2716])).
% 7.80/2.63  tff(c_2731, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2729])).
% 7.80/2.63  tff(c_2733, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2731, c_8])).
% 7.80/2.63  tff(c_2736, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4' | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_2717, c_2730, c_2733])).
% 7.80/2.63  tff(c_2738, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2736])).
% 7.80/2.63  tff(c_2741, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2738])).
% 7.80/2.63  tff(c_2744, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_2741])).
% 7.80/2.63  tff(c_2746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2744])).
% 7.80/2.63  tff(c_2747, plain, (k4_tmap_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_2736])).
% 7.80/2.63  tff(c_2752, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2747, c_42])).
% 7.80/2.63  tff(c_2758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_2752])).
% 7.80/2.63  tff(c_2760, plain, (~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_2729])).
% 7.80/2.63  tff(c_2836, plain, (![B_588, A_589, B_590, D_591]: (m1_subset_1('#skF_1'(B_588, A_589, B_590, k4_tmap_1(A_589, B_590), D_591), u1_struct_0(B_588)) | r2_funct_2(u1_struct_0(B_590), u1_struct_0(A_589), k2_tmap_1(B_588, A_589, D_591, B_590), k4_tmap_1(A_589, B_590)) | ~v1_funct_2(k4_tmap_1(A_589, B_590), u1_struct_0(B_590), u1_struct_0(A_589)) | ~v1_funct_1(k4_tmap_1(A_589, B_590)) | ~m1_subset_1(D_591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_588), u1_struct_0(A_589)))) | ~v1_funct_2(D_591, u1_struct_0(B_588), u1_struct_0(A_589)) | ~v1_funct_1(D_591) | ~m1_pre_topc(B_590, B_588) | v2_struct_0(B_590) | ~l1_pre_topc(B_588) | ~v2_pre_topc(B_588) | v2_struct_0(B_588) | ~m1_pre_topc(B_590, A_589) | ~l1_pre_topc(A_589) | ~v2_pre_topc(A_589) | v2_struct_0(A_589))), inference(resolution, [status(thm)], [c_24, c_206])).
% 7.80/2.63  tff(c_2847, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2557, c_2836])).
% 7.80/2.63  tff(c_2852, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_2717, c_2730, c_2847])).
% 7.80/2.63  tff(c_2853, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2760, c_2852])).
% 7.80/2.63  tff(c_2860, plain, (![A_19]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_19)) | ~m1_pre_topc('#skF_3', A_19) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(resolution, [status(thm)], [c_2853, c_16])).
% 7.80/2.63  tff(c_2922, plain, (![A_592]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_592)) | ~m1_pre_topc('#skF_3', A_592) | ~l1_pre_topc(A_592) | v2_struct_0(A_592))), inference(negUnitSimplification, [status(thm)], [c_54, c_2860])).
% 7.80/2.63  tff(c_2759, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2729])).
% 7.80/2.63  tff(c_2782, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2759, c_44])).
% 7.80/2.63  tff(c_2783, plain, (~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_2782])).
% 7.80/2.63  tff(c_2928, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2922, c_2783])).
% 7.80/2.63  tff(c_2936, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_2928])).
% 7.80/2.63  tff(c_2938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2936])).
% 7.80/2.63  tff(c_2940, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_2782])).
% 7.80/2.63  tff(c_2775, plain, (![A_98]: (k1_funct_1(k4_tmap_1(A_98, '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_98)) | ~m1_pre_topc('#skF_3', A_98) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_2759, c_40])).
% 7.80/2.63  tff(c_3014, plain, (![A_601]: (k1_funct_1(k4_tmap_1(A_601, '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_601)) | ~m1_pre_topc('#skF_3', A_601) | ~l1_pre_topc(A_601) | ~v2_pre_topc(A_601) | v2_struct_0(A_601))), inference(negUnitSimplification, [status(thm)], [c_54, c_2775])).
% 7.80/2.63  tff(c_3028, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2940, c_3014])).
% 7.80/2.63  tff(c_3037, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_3028])).
% 7.80/2.63  tff(c_3038, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_3037])).
% 7.80/2.63  tff(c_2982, plain, (![B_596, A_597, B_598, D_599]: (m1_subset_1('#skF_1'(B_596, A_597, B_598, k4_tmap_1(A_597, B_598), D_599), u1_struct_0(B_596)) | r2_funct_2(u1_struct_0(B_598), u1_struct_0(A_597), k2_tmap_1(B_596, A_597, D_599, B_598), k4_tmap_1(A_597, B_598)) | ~v1_funct_2(k4_tmap_1(A_597, B_598), u1_struct_0(B_598), u1_struct_0(A_597)) | ~v1_funct_1(k4_tmap_1(A_597, B_598)) | ~m1_subset_1(D_599, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_596), u1_struct_0(A_597)))) | ~v1_funct_2(D_599, u1_struct_0(B_596), u1_struct_0(A_597)) | ~v1_funct_1(D_599) | ~m1_pre_topc(B_598, B_596) | v2_struct_0(B_598) | ~l1_pre_topc(B_596) | ~v2_pre_topc(B_596) | v2_struct_0(B_596) | ~m1_pre_topc(B_598, A_597) | ~l1_pre_topc(A_597) | ~v2_pre_topc(A_597) | v2_struct_0(A_597))), inference(resolution, [status(thm)], [c_24, c_206])).
% 7.80/2.63  tff(c_2991, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2557, c_2982])).
% 7.80/2.63  tff(c_2996, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_84, c_73, c_250, c_50, c_48, c_46, c_2717, c_2730, c_2991])).
% 7.80/2.63  tff(c_2997, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2760, c_2996])).
% 7.80/2.63  tff(c_3002, plain, (![B_5, C_6]: (k3_funct_2(u1_struct_0('#skF_3'), B_5, C_6, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(C_6, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), B_5))) | ~v1_funct_2(C_6, u1_struct_0('#skF_3'), B_5) | ~v1_funct_1(C_6) | v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_2997, c_4])).
% 7.80/2.63  tff(c_3101, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3002])).
% 7.80/2.63  tff(c_3103, plain, (![A_1, B_126]: (~r2_hidden(A_1, u1_struct_0(B_126)) | ~m1_pre_topc(B_126, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_3101, c_93])).
% 7.80/2.63  tff(c_3107, plain, (![A_611, B_612]: (~r2_hidden(A_611, u1_struct_0(B_612)) | ~m1_pre_topc(B_612, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_3103])).
% 7.80/2.63  tff(c_3110, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_2759, c_3107])).
% 7.80/2.63  tff(c_3114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_3110])).
% 7.80/2.63  tff(c_3116, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_3002])).
% 7.80/2.63  tff(c_2939, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_2782])).
% 7.80/2.63  tff(c_3001, plain, (![A_19]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_19)) | ~m1_pre_topc('#skF_3', A_19) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(resolution, [status(thm)], [c_2997, c_16])).
% 7.80/2.63  tff(c_3007, plain, (![A_600]: (m1_subset_1('#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'), u1_struct_0(A_600)) | ~m1_pre_topc('#skF_3', A_600) | ~l1_pre_topc(A_600) | v2_struct_0(A_600))), inference(negUnitSimplification, [status(thm)], [c_54, c_3001])).
% 7.80/2.63  tff(c_3117, plain, (![A_613, B_614, C_615]: (k3_funct_2(u1_struct_0(A_613), B_614, C_615, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1(C_615, '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~m1_subset_1(C_615, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_613), B_614))) | ~v1_funct_2(C_615, u1_struct_0(A_613), B_614) | ~v1_funct_1(C_615) | v1_xboole_0(u1_struct_0(A_613)) | ~m1_pre_topc('#skF_3', A_613) | ~l1_pre_topc(A_613) | v2_struct_0(A_613))), inference(resolution, [status(thm)], [c_3007, c_4])).
% 7.80/2.63  tff(c_3126, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_3117])).
% 7.80/2.63  tff(c_3131, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_250, c_50, c_48, c_2939, c_3126])).
% 7.80/2.63  tff(c_3132, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_3131])).
% 7.80/2.63  tff(c_3133, plain, (k3_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_3116, c_3132])).
% 7.80/2.63  tff(c_3136, plain, (k1_funct_1(k4_tmap_1('#skF_2', '#skF_3'), '#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4'))!='#skF_1'('#skF_3', '#skF_2', '#skF_3', k4_tmap_1('#skF_2', '#skF_3'), '#skF_4') | r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k2_tmap_1('#skF_3', '#skF_2', '#skF_4', '#skF_3'), k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k4_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3133, c_34])).
% 7.80/2.63  tff(c_3140, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), '#skF_4', k4_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_84, c_73, c_250, c_50, c_48, c_46, c_2717, c_2730, c_2557, c_3038, c_3136])).
% 7.80/2.63  tff(c_3141, plain, (~m1_subset_1(k4_tmap_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_54, c_2760, c_3140])).
% 7.80/2.63  tff(c_3145, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3141])).
% 7.80/2.63  tff(c_3148, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_3145])).
% 7.80/2.63  tff(c_3150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3148])).
% 7.80/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/2.63  
% 7.80/2.63  Inference rules
% 7.80/2.63  ----------------------
% 7.80/2.63  #Ref     : 0
% 7.80/2.63  #Sup     : 553
% 7.80/2.63  #Fact    : 0
% 7.80/2.63  #Define  : 0
% 7.80/2.63  #Split   : 54
% 7.80/2.63  #Chain   : 0
% 7.80/2.63  #Close   : 0
% 7.80/2.63  
% 7.80/2.63  Ordering : KBO
% 7.80/2.63  
% 7.80/2.63  Simplification rules
% 7.80/2.63  ----------------------
% 7.80/2.63  #Subsume      : 55
% 7.80/2.63  #Demod        : 1359
% 7.80/2.63  #Tautology    : 203
% 7.80/2.63  #SimpNegUnit  : 152
% 7.80/2.63  #BackRed      : 33
% 7.80/2.63  
% 7.80/2.63  #Partial instantiations: 0
% 7.80/2.63  #Strategies tried      : 1
% 7.80/2.63  
% 7.80/2.63  Timing (in seconds)
% 7.80/2.63  ----------------------
% 7.80/2.64  Preprocessing        : 0.41
% 7.80/2.64  Parsing              : 0.22
% 7.80/2.64  CNF conversion       : 0.04
% 7.80/2.64  Main loop            : 1.39
% 7.80/2.64  Inferencing          : 0.49
% 7.80/2.64  Reduction            : 0.42
% 7.80/2.64  Demodulation         : 0.30
% 7.80/2.64  BG Simplification    : 0.05
% 7.80/2.64  Subsumption          : 0.33
% 7.80/2.64  Abstraction          : 0.06
% 7.80/2.64  MUC search           : 0.00
% 7.80/2.64  Cooper               : 0.00
% 7.80/2.64  Total                : 1.90
% 7.80/2.64  Index Insertion      : 0.00
% 7.80/2.64  Index Deletion       : 0.00
% 7.80/2.64  Index Matching       : 0.00
% 7.80/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
