%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:45 EST 2020

% Result     : Theorem 12.03s
% Output     : CNFRefutation 12.19s
% Verified   : 
% Statistics : Number of formulae       :  345 (30639 expanded)
%              Number of leaves         :   43 (12039 expanded)
%              Depth                    :   38
%              Number of atoms          : 1556 (207233 expanded)
%              Number of equality atoms :  114 (15135 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(f_333,negated_conjecture,(
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

tff(f_186,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k4_tmap_1(A,B))
        & v1_funct_2(k4_tmap_1(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(k4_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_tmap_1)).

tff(f_66,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_197,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_171,axiom,(
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

tff(f_271,axiom,(
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

tff(f_141,axiom,(
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

tff(f_109,axiom,(
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

tff(f_241,axiom,(
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

tff(f_193,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_303,axiom,(
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

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_28,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k4_tmap_1(A_73,B_74),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_74),u1_struct_0(A_73))))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_136,plain,(
    ! [A_210,B_211,D_212] :
      ( r2_funct_2(A_210,B_211,D_212,D_212)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ v1_funct_2(D_212,A_210,B_211)
      | ~ v1_funct_1(D_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_138,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_136])).

tff(c_141,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_138])).

tff(c_32,plain,(
    ! [A_73,B_74] :
      ( v1_funct_1(k4_tmap_1(A_73,B_74))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_87,plain,(
    ! [B_188,A_189] :
      ( v2_pre_topc(B_188)
      | ~ m1_pre_topc(B_188,A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_87])).

tff(c_97,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_93])).

tff(c_76,plain,(
    ! [B_186,A_187] :
      ( l1_pre_topc(B_186)
      | ~ m1_pre_topc(B_186,A_187)
      | ~ l1_pre_topc(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_76])).

tff(c_86,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_82])).

tff(c_36,plain,(
    ! [A_78] :
      ( m1_pre_topc(A_78,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_3389,plain,(
    ! [C_658,A_661,B_659,D_657,E_660] :
      ( v1_funct_1(k3_tmap_1(A_661,B_659,C_658,D_657,E_660))
      | ~ m1_subset_1(E_660,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_658),u1_struct_0(B_659))))
      | ~ v1_funct_2(E_660,u1_struct_0(C_658),u1_struct_0(B_659))
      | ~ v1_funct_1(E_660)
      | ~ m1_pre_topc(D_657,A_661)
      | ~ m1_pre_topc(C_658,A_661)
      | ~ l1_pre_topc(B_659)
      | ~ v2_pre_topc(B_659)
      | v2_struct_0(B_659)
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_3393,plain,(
    ! [A_661,D_657] :
      ( v1_funct_1(k3_tmap_1(A_661,'#skF_3','#skF_4',D_657,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_657,A_661)
      | ~ m1_pre_topc('#skF_4',A_661)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(resolution,[status(thm)],[c_54,c_3389])).

tff(c_3397,plain,(
    ! [A_661,D_657] :
      ( v1_funct_1(k3_tmap_1(A_661,'#skF_3','#skF_4',D_657,'#skF_5'))
      | ~ m1_pre_topc(D_657,A_661)
      | ~ m1_pre_topc('#skF_4',A_661)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_3393])).

tff(c_3398,plain,(
    ! [A_661,D_657] :
      ( v1_funct_1(k3_tmap_1(A_661,'#skF_3','#skF_4',D_657,'#skF_5'))
      | ~ m1_pre_topc(D_657,A_661)
      | ~ m1_pre_topc('#skF_4',A_661)
      | ~ l1_pre_topc(A_661)
      | ~ v2_pre_topc(A_661)
      | v2_struct_0(A_661) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3397])).

tff(c_3440,plain,(
    ! [A_686,B_684,E_685,C_683,D_682] :
      ( v1_funct_2(k3_tmap_1(A_686,B_684,C_683,D_682,E_685),u1_struct_0(D_682),u1_struct_0(B_684))
      | ~ m1_subset_1(E_685,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_683),u1_struct_0(B_684))))
      | ~ v1_funct_2(E_685,u1_struct_0(C_683),u1_struct_0(B_684))
      | ~ v1_funct_1(E_685)
      | ~ m1_pre_topc(D_682,A_686)
      | ~ m1_pre_topc(C_683,A_686)
      | ~ l1_pre_topc(B_684)
      | ~ v2_pre_topc(B_684)
      | v2_struct_0(B_684)
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_3444,plain,(
    ! [A_686,D_682] :
      ( v1_funct_2(k3_tmap_1(A_686,'#skF_3','#skF_4',D_682,'#skF_5'),u1_struct_0(D_682),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_682,A_686)
      | ~ m1_pre_topc('#skF_4',A_686)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(resolution,[status(thm)],[c_54,c_3440])).

tff(c_3448,plain,(
    ! [A_686,D_682] :
      ( v1_funct_2(k3_tmap_1(A_686,'#skF_3','#skF_4',D_682,'#skF_5'),u1_struct_0(D_682),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_682,A_686)
      | ~ m1_pre_topc('#skF_4',A_686)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_3444])).

tff(c_3449,plain,(
    ! [A_686,D_682] :
      ( v1_funct_2(k3_tmap_1(A_686,'#skF_3','#skF_4',D_682,'#skF_5'),u1_struct_0(D_682),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_682,A_686)
      | ~ m1_pre_topc('#skF_4',A_686)
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3448])).

tff(c_22,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_3423,plain,(
    ! [C_673,B_674,D_675,A_676] :
      ( r2_funct_2(u1_struct_0(C_673),u1_struct_0(B_674),D_675,k3_tmap_1(A_676,B_674,C_673,C_673,D_675))
      | ~ m1_subset_1(D_675,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_673),u1_struct_0(B_674))))
      | ~ v1_funct_2(D_675,u1_struct_0(C_673),u1_struct_0(B_674))
      | ~ v1_funct_1(D_675)
      | ~ m1_pre_topc(C_673,A_676)
      | v2_struct_0(C_673)
      | ~ l1_pre_topc(B_674)
      | ~ v2_pre_topc(B_674)
      | v2_struct_0(B_674)
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676)
      | v2_struct_0(A_676) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_3427,plain,(
    ! [A_676] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_676,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_676)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676)
      | v2_struct_0(A_676) ) ),
    inference(resolution,[status(thm)],[c_54,c_3423])).

tff(c_3431,plain,(
    ! [A_676] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_676,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_676)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_676)
      | ~ v2_pre_topc(A_676)
      | v2_struct_0(A_676) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_3427])).

tff(c_3433,plain,(
    ! [A_677] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_677,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_677)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_3431])).

tff(c_12,plain,(
    ! [D_15,C_14,A_12,B_13] :
      ( D_15 = C_14
      | ~ r2_funct_2(A_12,B_13,C_14,D_15)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(D_15,A_12,B_13)
      | ~ v1_funct_1(D_15)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(C_14,A_12,B_13)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3435,plain,(
    ! [A_677] :
      ( k3_tmap_1(A_677,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_677,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_677,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_677,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_677)
      | ~ l1_pre_topc(A_677)
      | ~ v2_pre_topc(A_677)
      | v2_struct_0(A_677) ) ),
    inference(resolution,[status(thm)],[c_3433,c_12])).

tff(c_3486,plain,(
    ! [A_701] :
      ( k3_tmap_1(A_701,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_701,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_701,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_701,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_701)
      | ~ l1_pre_topc(A_701)
      | ~ v2_pre_topc(A_701)
      | v2_struct_0(A_701) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_3435])).

tff(c_3490,plain,(
    ! [A_68] :
      ( k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_68)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_22,c_3486])).

tff(c_3493,plain,(
    ! [A_68] :
      ( k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_68)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_3490])).

tff(c_3495,plain,(
    ! [A_702] :
      ( k3_tmap_1(A_702,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_702,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_702,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_702)
      | ~ l1_pre_topc(A_702)
      | ~ v2_pre_topc(A_702)
      | v2_struct_0(A_702) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3493])).

tff(c_3501,plain,(
    ! [A_703] :
      ( k3_tmap_1(A_703,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_1(k3_tmap_1(A_703,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_703)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703)
      | v2_struct_0(A_703) ) ),
    inference(resolution,[status(thm)],[c_3449,c_3495])).

tff(c_3507,plain,(
    ! [A_704] :
      ( k3_tmap_1(A_704,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_pre_topc('#skF_4',A_704)
      | ~ l1_pre_topc(A_704)
      | ~ v2_pre_topc(A_704)
      | v2_struct_0(A_704) ) ),
    inference(resolution,[status(thm)],[c_3398,c_3501])).

tff(c_3514,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3507])).

tff(c_3521,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3514])).

tff(c_3522,plain,(
    k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3521])).

tff(c_3598,plain,(
    ! [A_716,B_717,C_715,D_718,E_714] :
      ( k3_tmap_1(A_716,B_717,C_715,D_718,E_714) = k2_partfun1(u1_struct_0(C_715),u1_struct_0(B_717),E_714,u1_struct_0(D_718))
      | ~ m1_pre_topc(D_718,C_715)
      | ~ m1_subset_1(E_714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_715),u1_struct_0(B_717))))
      | ~ v1_funct_2(E_714,u1_struct_0(C_715),u1_struct_0(B_717))
      | ~ v1_funct_1(E_714)
      | ~ m1_pre_topc(D_718,A_716)
      | ~ m1_pre_topc(C_715,A_716)
      | ~ l1_pre_topc(B_717)
      | ~ v2_pre_topc(B_717)
      | v2_struct_0(B_717)
      | ~ l1_pre_topc(A_716)
      | ~ v2_pre_topc(A_716)
      | v2_struct_0(A_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3604,plain,(
    ! [A_716,D_718] :
      ( k3_tmap_1(A_716,'#skF_3','#skF_4',D_718,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_718))
      | ~ m1_pre_topc(D_718,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_718,A_716)
      | ~ m1_pre_topc('#skF_4',A_716)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_716)
      | ~ v2_pre_topc(A_716)
      | v2_struct_0(A_716) ) ),
    inference(resolution,[status(thm)],[c_54,c_3598])).

tff(c_3609,plain,(
    ! [A_716,D_718] :
      ( k3_tmap_1(A_716,'#skF_3','#skF_4',D_718,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_718))
      | ~ m1_pre_topc(D_718,'#skF_4')
      | ~ m1_pre_topc(D_718,A_716)
      | ~ m1_pre_topc('#skF_4',A_716)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_716)
      | ~ v2_pre_topc(A_716)
      | v2_struct_0(A_716) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_3604])).

tff(c_3611,plain,(
    ! [A_719,D_720] :
      ( k3_tmap_1(A_719,'#skF_3','#skF_4',D_720,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_720))
      | ~ m1_pre_topc(D_720,'#skF_4')
      | ~ m1_pre_topc(D_720,A_719)
      | ~ m1_pre_topc('#skF_4',A_719)
      | ~ l1_pre_topc(A_719)
      | ~ v2_pre_topc(A_719)
      | v2_struct_0(A_719) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3609])).

tff(c_3615,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_3611])).

tff(c_3619,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_3522,c_3615])).

tff(c_3620,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3619])).

tff(c_3621,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3620])).

tff(c_3624,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3621])).

tff(c_3628,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_3624])).

tff(c_3630,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3620])).

tff(c_3629,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3620])).

tff(c_3399,plain,(
    ! [A_662,B_663,C_664,D_665] :
      ( k2_partfun1(u1_struct_0(A_662),u1_struct_0(B_663),C_664,u1_struct_0(D_665)) = k2_tmap_1(A_662,B_663,C_664,D_665)
      | ~ m1_pre_topc(D_665,A_662)
      | ~ m1_subset_1(C_664,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_662),u1_struct_0(B_663))))
      | ~ v1_funct_2(C_664,u1_struct_0(A_662),u1_struct_0(B_663))
      | ~ v1_funct_1(C_664)
      | ~ l1_pre_topc(B_663)
      | ~ v2_pre_topc(B_663)
      | v2_struct_0(B_663)
      | ~ l1_pre_topc(A_662)
      | ~ v2_pre_topc(A_662)
      | v2_struct_0(A_662) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3403,plain,(
    ! [D_665] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_665)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_665)
      | ~ m1_pre_topc(D_665,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_3399])).

tff(c_3407,plain,(
    ! [D_665] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_665)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_665)
      | ~ m1_pre_topc(D_665,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_86,c_66,c_64,c_58,c_56,c_3403])).

tff(c_3408,plain,(
    ! [D_665] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_665)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_665)
      | ~ m1_pre_topc(D_665,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_3407])).

tff(c_3662,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3629,c_3408])).

tff(c_3669,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3630,c_3662])).

tff(c_3731,plain,(
    ! [A_723,C_722,B_726,D_725,E_724] :
      ( m1_subset_1('#skF_2'(C_722,A_723,E_724,D_725,B_726),u1_struct_0(B_726))
      | r2_funct_2(u1_struct_0(C_722),u1_struct_0(A_723),k2_tmap_1(B_726,A_723,D_725,C_722),E_724)
      | ~ m1_subset_1(E_724,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_722),u1_struct_0(A_723))))
      | ~ v1_funct_2(E_724,u1_struct_0(C_722),u1_struct_0(A_723))
      | ~ v1_funct_1(E_724)
      | ~ m1_subset_1(D_725,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_726),u1_struct_0(A_723))))
      | ~ v1_funct_2(D_725,u1_struct_0(B_726),u1_struct_0(A_723))
      | ~ v1_funct_1(D_725)
      | ~ m1_pre_topc(C_722,B_726)
      | v2_struct_0(C_722)
      | ~ l1_pre_topc(B_726)
      | ~ v2_pre_topc(B_726)
      | v2_struct_0(B_726)
      | ~ l1_pre_topc(A_723)
      | ~ v2_pre_topc(A_723)
      | v2_struct_0(A_723) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_4679,plain,(
    ! [B_829,A_830,D_831,B_832] :
      ( m1_subset_1('#skF_2'(B_829,A_830,k4_tmap_1(A_830,B_829),D_831,B_832),u1_struct_0(B_832))
      | r2_funct_2(u1_struct_0(B_829),u1_struct_0(A_830),k2_tmap_1(B_832,A_830,D_831,B_829),k4_tmap_1(A_830,B_829))
      | ~ v1_funct_2(k4_tmap_1(A_830,B_829),u1_struct_0(B_829),u1_struct_0(A_830))
      | ~ v1_funct_1(k4_tmap_1(A_830,B_829))
      | ~ m1_subset_1(D_831,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_832),u1_struct_0(A_830))))
      | ~ v1_funct_2(D_831,u1_struct_0(B_832),u1_struct_0(A_830))
      | ~ v1_funct_1(D_831)
      | ~ m1_pre_topc(B_829,B_832)
      | v2_struct_0(B_829)
      | ~ l1_pre_topc(B_832)
      | ~ v2_pre_topc(B_832)
      | v2_struct_0(B_832)
      | ~ m1_pre_topc(B_829,A_830)
      | ~ l1_pre_topc(A_830)
      | ~ v2_pre_topc(A_830)
      | v2_struct_0(A_830) ) ),
    inference(resolution,[status(thm)],[c_28,c_3731])).

tff(c_4686,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3669,c_4679])).

tff(c_4690,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_97,c_86,c_3630,c_58,c_56,c_54,c_4686])).

tff(c_4691,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_4690])).

tff(c_4692,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4691])).

tff(c_4695,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_4692])).

tff(c_4698,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_4695])).

tff(c_4700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4698])).

tff(c_4702,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4691])).

tff(c_30,plain,(
    ! [A_73,B_74] :
      ( v1_funct_2(k4_tmap_1(A_73,B_74),u1_struct_0(B_74),u1_struct_0(A_73))
      | ~ m1_pre_topc(B_74,A_73)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_4701,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4691])).

tff(c_4719,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4701])).

tff(c_4722,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_4719])).

tff(c_4725,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_4722])).

tff(c_4727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4725])).

tff(c_4729,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4701])).

tff(c_4728,plain,
    ( m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4701])).

tff(c_4730,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4728])).

tff(c_4732,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4730,c_12])).

tff(c_4735,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_4702,c_4729,c_4732])).

tff(c_4746,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_4735])).

tff(c_4749,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_4746])).

tff(c_4752,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_4749])).

tff(c_4754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4752])).

tff(c_4755,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4735])).

tff(c_50,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k4_tmap_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_4761,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4755,c_50])).

tff(c_4768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_4761])).

tff(c_4770,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4728])).

tff(c_3902,plain,(
    ! [A_737,B_740,D_739,C_736,E_738] :
      ( r2_hidden('#skF_2'(C_736,A_737,E_738,D_739,B_740),u1_struct_0(C_736))
      | r2_funct_2(u1_struct_0(C_736),u1_struct_0(A_737),k2_tmap_1(B_740,A_737,D_739,C_736),E_738)
      | ~ m1_subset_1(E_738,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_736),u1_struct_0(A_737))))
      | ~ v1_funct_2(E_738,u1_struct_0(C_736),u1_struct_0(A_737))
      | ~ v1_funct_1(E_738)
      | ~ m1_subset_1(D_739,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_740),u1_struct_0(A_737))))
      | ~ v1_funct_2(D_739,u1_struct_0(B_740),u1_struct_0(A_737))
      | ~ v1_funct_1(D_739)
      | ~ m1_pre_topc(C_736,B_740)
      | v2_struct_0(C_736)
      | ~ l1_pre_topc(B_740)
      | ~ v2_pre_topc(B_740)
      | v2_struct_0(B_740)
      | ~ l1_pre_topc(A_737)
      | ~ v2_pre_topc(A_737)
      | v2_struct_0(A_737) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_4837,plain,(
    ! [B_844,A_845,D_846,B_847] :
      ( r2_hidden('#skF_2'(B_844,A_845,k4_tmap_1(A_845,B_844),D_846,B_847),u1_struct_0(B_844))
      | r2_funct_2(u1_struct_0(B_844),u1_struct_0(A_845),k2_tmap_1(B_847,A_845,D_846,B_844),k4_tmap_1(A_845,B_844))
      | ~ v1_funct_2(k4_tmap_1(A_845,B_844),u1_struct_0(B_844),u1_struct_0(A_845))
      | ~ v1_funct_1(k4_tmap_1(A_845,B_844))
      | ~ m1_subset_1(D_846,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_847),u1_struct_0(A_845))))
      | ~ v1_funct_2(D_846,u1_struct_0(B_847),u1_struct_0(A_845))
      | ~ v1_funct_1(D_846)
      | ~ m1_pre_topc(B_844,B_847)
      | v2_struct_0(B_844)
      | ~ l1_pre_topc(B_847)
      | ~ v2_pre_topc(B_847)
      | v2_struct_0(B_847)
      | ~ m1_pre_topc(B_844,A_845)
      | ~ l1_pre_topc(A_845)
      | ~ v2_pre_topc(A_845)
      | v2_struct_0(A_845) ) ),
    inference(resolution,[status(thm)],[c_28,c_3902])).

tff(c_4842,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3669,c_4837])).

tff(c_4845,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_97,c_86,c_3630,c_58,c_56,c_54,c_4702,c_4729,c_4842])).

tff(c_4846,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_4770,c_4845])).

tff(c_103,plain,(
    ! [B_194,A_195] :
      ( m1_subset_1(u1_struct_0(B_194),k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_pre_topc(B_194,A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [A_5,A_195,B_194] :
      ( m1_subset_1(A_5,u1_struct_0(A_195))
      | ~ r2_hidden(A_5,u1_struct_0(B_194))
      | ~ m1_pre_topc(B_194,A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(resolution,[status(thm)],[c_103,c_6])).

tff(c_4860,plain,(
    ! [A_195] :
      ( m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0(A_195))
      | ~ m1_pre_topc('#skF_4',A_195)
      | ~ l1_pre_topc(A_195) ) ),
    inference(resolution,[status(thm)],[c_4846,c_106])).

tff(c_52,plain,(
    ! [D_181] :
      ( k1_funct_1('#skF_5',D_181) = D_181
      | ~ r2_hidden(D_181,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_181,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_4861,plain,
    ( k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4846,c_52])).

tff(c_4868,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4861])).

tff(c_4871,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4860,c_4868])).

tff(c_4875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_4871])).

tff(c_4876,plain,(
    k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_4861])).

tff(c_3511,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3507])).

tff(c_3517,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_97,c_3511])).

tff(c_3518,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3517])).

tff(c_3616,plain,(
    ! [A_78] :
      ( k3_tmap_1(A_78,'#skF_3','#skF_4',A_78,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_78))
      | ~ m1_pre_topc(A_78,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_36,c_3611])).

tff(c_3679,plain,(
    ! [A_721] :
      ( k3_tmap_1(A_721,'#skF_3','#skF_4',A_721,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_721))
      | ~ m1_pre_topc(A_721,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_721)
      | ~ v2_pre_topc(A_721)
      | v2_struct_0(A_721)
      | ~ l1_pre_topc(A_721) ) ),
    inference(resolution,[status(thm)],[c_36,c_3611])).

tff(c_3693,plain,(
    ! [A_721] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_721)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_721),u1_struct_0('#skF_3'))))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(A_721,A_721)
      | ~ m1_pre_topc('#skF_4',A_721)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_721)
      | ~ v2_pre_topc(A_721)
      | v2_struct_0(A_721)
      | ~ m1_pre_topc(A_721,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_721)
      | ~ v2_pre_topc(A_721)
      | v2_struct_0(A_721)
      | ~ l1_pre_topc(A_721) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3679,c_22])).

tff(c_3724,plain,(
    ! [A_721] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_721)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_721),u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_721,A_721)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(A_721,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_721)
      | ~ v2_pre_topc(A_721)
      | v2_struct_0(A_721)
      | ~ l1_pre_topc(A_721) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_3693])).

tff(c_3758,plain,(
    ! [A_728] :
      ( m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(A_728)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_728),u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_728,A_728)
      | ~ m1_pre_topc(A_728,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_728)
      | ~ v2_pre_topc(A_728)
      | v2_struct_0(A_728)
      | ~ l1_pre_topc(A_728) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3724])).

tff(c_3781,plain,(
    ! [A_78] :
      ( m1_subset_1(k3_tmap_1(A_78,'#skF_3','#skF_4',A_78,'#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78),u1_struct_0('#skF_3'))))
      | ~ m1_pre_topc(A_78,A_78)
      | ~ m1_pre_topc(A_78,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ l1_pre_topc(A_78)
      | ~ m1_pre_topc(A_78,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3616,c_3758])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_203,A_204,B_205] :
      ( m1_subset_1(A_203,u1_struct_0(A_204))
      | ~ r2_hidden(A_203,u1_struct_0(B_205))
      | ~ m1_pre_topc(B_205,A_204)
      | ~ l1_pre_topc(A_204) ) ),
    inference(resolution,[status(thm)],[c_103,c_6])).

tff(c_133,plain,(
    ! [B_205,A_204] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_205)),u1_struct_0(A_204))
      | ~ m1_pre_topc(B_205,A_204)
      | ~ l1_pre_topc(A_204)
      | v1_xboole_0(u1_struct_0(B_205)) ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_107,plain,(
    ! [D_196] :
      ( k1_funct_1('#skF_5',D_196) = D_196
      | ~ r2_hidden(D_196,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_196,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_333])).

tff(c_112,plain,
    ( k1_funct_1('#skF_5','#skF_1'(u1_struct_0('#skF_4'))) = '#skF_1'(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4')),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_107])).

tff(c_142,plain,(
    ~ m1_subset_1('#skF_1'(u1_struct_0('#skF_4')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_145,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_133,c_142])).

tff(c_148,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_145])).

tff(c_217,plain,(
    ! [C_244,B_245,D_243,E_246,A_247] :
      ( v1_funct_1(k3_tmap_1(A_247,B_245,C_244,D_243,E_246))
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_244),u1_struct_0(B_245))))
      | ~ v1_funct_2(E_246,u1_struct_0(C_244),u1_struct_0(B_245))
      | ~ v1_funct_1(E_246)
      | ~ m1_pre_topc(D_243,A_247)
      | ~ m1_pre_topc(C_244,A_247)
      | ~ l1_pre_topc(B_245)
      | ~ v2_pre_topc(B_245)
      | v2_struct_0(B_245)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_221,plain,(
    ! [A_247,D_243] :
      ( v1_funct_1(k3_tmap_1(A_247,'#skF_3','#skF_4',D_243,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_243,A_247)
      | ~ m1_pre_topc('#skF_4',A_247)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(resolution,[status(thm)],[c_54,c_217])).

tff(c_225,plain,(
    ! [A_247,D_243] :
      ( v1_funct_1(k3_tmap_1(A_247,'#skF_3','#skF_4',D_243,'#skF_5'))
      | ~ m1_pre_topc(D_243,A_247)
      | ~ m1_pre_topc('#skF_4',A_247)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_221])).

tff(c_226,plain,(
    ! [A_247,D_243] :
      ( v1_funct_1(k3_tmap_1(A_247,'#skF_3','#skF_4',D_243,'#skF_5'))
      | ~ m1_pre_topc(D_243,A_247)
      | ~ m1_pre_topc('#skF_4',A_247)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247)
      | v2_struct_0(A_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_225])).

tff(c_248,plain,(
    ! [C_256,D_255,E_258,A_259,B_257] :
      ( v1_funct_2(k3_tmap_1(A_259,B_257,C_256,D_255,E_258),u1_struct_0(D_255),u1_struct_0(B_257))
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256),u1_struct_0(B_257))))
      | ~ v1_funct_2(E_258,u1_struct_0(C_256),u1_struct_0(B_257))
      | ~ v1_funct_1(E_258)
      | ~ m1_pre_topc(D_255,A_259)
      | ~ m1_pre_topc(C_256,A_259)
      | ~ l1_pre_topc(B_257)
      | ~ v2_pre_topc(B_257)
      | v2_struct_0(B_257)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_252,plain,(
    ! [A_259,D_255] :
      ( v1_funct_2(k3_tmap_1(A_259,'#skF_3','#skF_4',D_255,'#skF_5'),u1_struct_0(D_255),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_255,A_259)
      | ~ m1_pre_topc('#skF_4',A_259)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_54,c_248])).

tff(c_256,plain,(
    ! [A_259,D_255] :
      ( v1_funct_2(k3_tmap_1(A_259,'#skF_3','#skF_4',D_255,'#skF_5'),u1_struct_0(D_255),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_255,A_259)
      | ~ m1_pre_topc('#skF_4',A_259)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_252])).

tff(c_257,plain,(
    ! [A_259,D_255] :
      ( v1_funct_2(k3_tmap_1(A_259,'#skF_3','#skF_4',D_255,'#skF_5'),u1_struct_0(D_255),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_255,A_259)
      | ~ m1_pre_topc('#skF_4',A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_256])).

tff(c_264,plain,(
    ! [C_270,B_271,D_272,A_273] :
      ( r2_funct_2(u1_struct_0(C_270),u1_struct_0(B_271),D_272,k3_tmap_1(A_273,B_271,C_270,C_270,D_272))
      | ~ m1_subset_1(D_272,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_270),u1_struct_0(B_271))))
      | ~ v1_funct_2(D_272,u1_struct_0(C_270),u1_struct_0(B_271))
      | ~ v1_funct_1(D_272)
      | ~ m1_pre_topc(C_270,A_273)
      | v2_struct_0(C_270)
      | ~ l1_pre_topc(B_271)
      | ~ v2_pre_topc(B_271)
      | v2_struct_0(B_271)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_268,plain,(
    ! [A_273] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_273,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_273)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_54,c_264])).

tff(c_272,plain,(
    ! [A_273] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_273,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_273)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_268])).

tff(c_274,plain,(
    ! [A_274] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_274,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_272])).

tff(c_276,plain,(
    ! [A_274] :
      ( k3_tmap_1(A_274,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_274,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_274,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_274,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_274,c_12])).

tff(c_315,plain,(
    ! [A_287] :
      ( k3_tmap_1(A_287,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_subset_1(k3_tmap_1(A_287,'#skF_3','#skF_4','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(k3_tmap_1(A_287,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_287,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_287)
      | ~ l1_pre_topc(A_287)
      | ~ v2_pre_topc(A_287)
      | v2_struct_0(A_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_276])).

tff(c_319,plain,(
    ! [A_68] :
      ( k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_68)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_22,c_315])).

tff(c_322,plain,(
    ! [A_68] :
      ( k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_68,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_68)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_54,c_319])).

tff(c_324,plain,(
    ! [A_288] :
      ( k3_tmap_1(A_288,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_2(k3_tmap_1(A_288,'#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(k3_tmap_1(A_288,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_322])).

tff(c_330,plain,(
    ! [A_289] :
      ( k3_tmap_1(A_289,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ v1_funct_1(k3_tmap_1(A_289,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_289)
      | ~ l1_pre_topc(A_289)
      | ~ v2_pre_topc(A_289)
      | v2_struct_0(A_289) ) ),
    inference(resolution,[status(thm)],[c_257,c_324])).

tff(c_336,plain,(
    ! [A_290] :
      ( k3_tmap_1(A_290,'#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
      | ~ m1_pre_topc('#skF_4',A_290)
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(resolution,[status(thm)],[c_226,c_330])).

tff(c_343,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_336])).

tff(c_350,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5'
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_343])).

tff(c_351,plain,(
    k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_350])).

tff(c_412,plain,(
    ! [A_296,B_297,C_295,D_298,E_294] :
      ( k3_tmap_1(A_296,B_297,C_295,D_298,E_294) = k2_partfun1(u1_struct_0(C_295),u1_struct_0(B_297),E_294,u1_struct_0(D_298))
      | ~ m1_pre_topc(D_298,C_295)
      | ~ m1_subset_1(E_294,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_295),u1_struct_0(B_297))))
      | ~ v1_funct_2(E_294,u1_struct_0(C_295),u1_struct_0(B_297))
      | ~ v1_funct_1(E_294)
      | ~ m1_pre_topc(D_298,A_296)
      | ~ m1_pre_topc(C_295,A_296)
      | ~ l1_pre_topc(B_297)
      | ~ v2_pre_topc(B_297)
      | v2_struct_0(B_297)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_418,plain,(
    ! [A_296,D_298] :
      ( k3_tmap_1(A_296,'#skF_3','#skF_4',D_298,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_298))
      | ~ m1_pre_topc(D_298,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_298,A_296)
      | ~ m1_pre_topc('#skF_4',A_296)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(resolution,[status(thm)],[c_54,c_412])).

tff(c_423,plain,(
    ! [A_296,D_298] :
      ( k3_tmap_1(A_296,'#skF_3','#skF_4',D_298,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_298))
      | ~ m1_pre_topc(D_298,'#skF_4')
      | ~ m1_pre_topc(D_298,A_296)
      | ~ m1_pre_topc('#skF_4',A_296)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_418])).

tff(c_425,plain,(
    ! [A_299,D_300] :
      ( k3_tmap_1(A_299,'#skF_3','#skF_4',D_300,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_300))
      | ~ m1_pre_topc(D_300,'#skF_4')
      | ~ m1_pre_topc(D_300,A_299)
      | ~ m1_pre_topc('#skF_4',A_299)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_423])).

tff(c_429,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_425])).

tff(c_433,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_351,c_429])).

tff(c_434,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_433])).

tff(c_435,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_438,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_435])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_438])).

tff(c_444,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_443,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_228,plain,(
    ! [A_250,B_251,C_252,D_253] :
      ( k2_partfun1(u1_struct_0(A_250),u1_struct_0(B_251),C_252,u1_struct_0(D_253)) = k2_tmap_1(A_250,B_251,C_252,D_253)
      | ~ m1_pre_topc(D_253,A_250)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_250),u1_struct_0(B_251))))
      | ~ v1_funct_2(C_252,u1_struct_0(A_250),u1_struct_0(B_251))
      | ~ v1_funct_1(C_252)
      | ~ l1_pre_topc(B_251)
      | ~ v2_pre_topc(B_251)
      | v2_struct_0(B_251)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_232,plain,(
    ! [D_253] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_253)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_253)
      | ~ m1_pre_topc(D_253,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_228])).

tff(c_236,plain,(
    ! [D_253] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_253)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_253)
      | ~ m1_pre_topc(D_253,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_86,c_66,c_64,c_58,c_56,c_232])).

tff(c_237,plain,(
    ! [D_253] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_253)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_253)
      | ~ m1_pre_topc(D_253,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_236])).

tff(c_476,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_237])).

tff(c_483,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_476])).

tff(c_748,plain,(
    ! [B_323,D_322,A_320,C_319,E_321] :
      ( r2_hidden('#skF_2'(C_319,A_320,E_321,D_322,B_323),u1_struct_0(C_319))
      | r2_funct_2(u1_struct_0(C_319),u1_struct_0(A_320),k2_tmap_1(B_323,A_320,D_322,C_319),E_321)
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_319),u1_struct_0(A_320))))
      | ~ v1_funct_2(E_321,u1_struct_0(C_319),u1_struct_0(A_320))
      | ~ v1_funct_1(E_321)
      | ~ m1_subset_1(D_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_323),u1_struct_0(A_320))))
      | ~ v1_funct_2(D_322,u1_struct_0(B_323),u1_struct_0(A_320))
      | ~ v1_funct_1(D_322)
      | ~ m1_pre_topc(C_319,B_323)
      | v2_struct_0(C_319)
      | ~ l1_pre_topc(B_323)
      | ~ v2_pre_topc(B_323)
      | v2_struct_0(B_323)
      | ~ l1_pre_topc(A_320)
      | ~ v2_pre_topc(A_320)
      | v2_struct_0(A_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_1508,plain,(
    ! [B_415,A_416,D_417,B_418] :
      ( r2_hidden('#skF_2'(B_415,A_416,k4_tmap_1(A_416,B_415),D_417,B_418),u1_struct_0(B_415))
      | r2_funct_2(u1_struct_0(B_415),u1_struct_0(A_416),k2_tmap_1(B_418,A_416,D_417,B_415),k4_tmap_1(A_416,B_415))
      | ~ v1_funct_2(k4_tmap_1(A_416,B_415),u1_struct_0(B_415),u1_struct_0(A_416))
      | ~ v1_funct_1(k4_tmap_1(A_416,B_415))
      | ~ m1_subset_1(D_417,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_418),u1_struct_0(A_416))))
      | ~ v1_funct_2(D_417,u1_struct_0(B_418),u1_struct_0(A_416))
      | ~ v1_funct_1(D_417)
      | ~ m1_pre_topc(B_415,B_418)
      | v2_struct_0(B_415)
      | ~ l1_pre_topc(B_418)
      | ~ v2_pre_topc(B_418)
      | v2_struct_0(B_418)
      | ~ m1_pre_topc(B_415,A_416)
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(resolution,[status(thm)],[c_28,c_748])).

tff(c_1513,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_1508])).

tff(c_1516,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_97,c_86,c_444,c_58,c_56,c_54,c_1513])).

tff(c_1517,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1516])).

tff(c_1518,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1517])).

tff(c_1521,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1518])).

tff(c_1524,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1521])).

tff(c_1526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1524])).

tff(c_1528,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_1527,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_1545,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1527])).

tff(c_1548,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1545])).

tff(c_1551,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1548])).

tff(c_1553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1551])).

tff(c_1555,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1527])).

tff(c_1554,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1527])).

tff(c_1556,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1554])).

tff(c_1558,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1556,c_12])).

tff(c_1561,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1528,c_1555,c_1558])).

tff(c_1575,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1561])).

tff(c_1578,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1575])).

tff(c_1581,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1578])).

tff(c_1583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1581])).

tff(c_1584,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1561])).

tff(c_1589,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_50])).

tff(c_1595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1589])).

tff(c_1596,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1554])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1617,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1596,c_2])).

tff(c_1626,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1617])).

tff(c_1628,plain,(
    m1_subset_1('#skF_1'(u1_struct_0('#skF_4')),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_1664,plain,(
    ! [A_437,B_438,C_439] :
      ( k1_funct_1(k4_tmap_1(A_437,B_438),C_439) = C_439
      | ~ r2_hidden(C_439,u1_struct_0(B_438))
      | ~ m1_subset_1(C_439,u1_struct_0(A_437))
      | ~ m1_pre_topc(B_438,A_437)
      | v2_struct_0(B_438)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_1670,plain,(
    ! [A_440,B_441] :
      ( k1_funct_1(k4_tmap_1(A_440,B_441),'#skF_1'(u1_struct_0(B_441))) = '#skF_1'(u1_struct_0(B_441))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_441)),u1_struct_0(A_440))
      | ~ m1_pre_topc(B_441,A_440)
      | v2_struct_0(B_441)
      | ~ l1_pre_topc(A_440)
      | ~ v2_pre_topc(A_440)
      | v2_struct_0(A_440)
      | v1_xboole_0(u1_struct_0(B_441)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1664])).

tff(c_1672,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'))) = '#skF_1'(u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1628,c_1670])).

tff(c_1677,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'))) = '#skF_1'(u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1672])).

tff(c_1678,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_1'(u1_struct_0('#skF_4'))) = '#skF_1'(u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1677])).

tff(c_1680,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1678])).

tff(c_1802,plain,(
    ! [E_499,C_500,D_503,A_501,B_502] :
      ( k3_tmap_1(A_501,B_502,C_500,D_503,E_499) = k2_partfun1(u1_struct_0(C_500),u1_struct_0(B_502),E_499,u1_struct_0(D_503))
      | ~ m1_pre_topc(D_503,C_500)
      | ~ m1_subset_1(E_499,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_500),u1_struct_0(B_502))))
      | ~ v1_funct_2(E_499,u1_struct_0(C_500),u1_struct_0(B_502))
      | ~ v1_funct_1(E_499)
      | ~ m1_pre_topc(D_503,A_501)
      | ~ m1_pre_topc(C_500,A_501)
      | ~ l1_pre_topc(B_502)
      | ~ v2_pre_topc(B_502)
      | v2_struct_0(B_502)
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1808,plain,(
    ! [A_501,D_503] :
      ( k3_tmap_1(A_501,'#skF_3','#skF_4',D_503,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_503))
      | ~ m1_pre_topc(D_503,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_503,A_501)
      | ~ m1_pre_topc('#skF_4',A_501)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501) ) ),
    inference(resolution,[status(thm)],[c_54,c_1802])).

tff(c_1813,plain,(
    ! [A_501,D_503] :
      ( k3_tmap_1(A_501,'#skF_3','#skF_4',D_503,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_503))
      | ~ m1_pre_topc(D_503,'#skF_4')
      | ~ m1_pre_topc(D_503,A_501)
      | ~ m1_pre_topc('#skF_4',A_501)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1808])).

tff(c_1815,plain,(
    ! [A_504,D_505] :
      ( k3_tmap_1(A_504,'#skF_3','#skF_4',D_505,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_505))
      | ~ m1_pre_topc(D_505,'#skF_4')
      | ~ m1_pre_topc(D_505,A_504)
      | ~ m1_pre_topc('#skF_4',A_504)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1813])).

tff(c_1819,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1815])).

tff(c_1823,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1819])).

tff(c_1824,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1823])).

tff(c_1825,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1824])).

tff(c_1828,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1825])).

tff(c_1832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1828])).

tff(c_1834,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1824])).

tff(c_1833,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1824])).

tff(c_1725,plain,(
    ! [A_465,B_466,C_467,D_468] :
      ( k2_partfun1(u1_struct_0(A_465),u1_struct_0(B_466),C_467,u1_struct_0(D_468)) = k2_tmap_1(A_465,B_466,C_467,D_468)
      | ~ m1_pre_topc(D_468,A_465)
      | ~ m1_subset_1(C_467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_465),u1_struct_0(B_466))))
      | ~ v1_funct_2(C_467,u1_struct_0(A_465),u1_struct_0(B_466))
      | ~ v1_funct_1(C_467)
      | ~ l1_pre_topc(B_466)
      | ~ v2_pre_topc(B_466)
      | v2_struct_0(B_466)
      | ~ l1_pre_topc(A_465)
      | ~ v2_pre_topc(A_465)
      | v2_struct_0(A_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1729,plain,(
    ! [D_468] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_468)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_468)
      | ~ m1_pre_topc(D_468,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_54,c_1725])).

tff(c_1733,plain,(
    ! [D_468] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_468)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_468)
      | ~ m1_pre_topc(D_468,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_86,c_66,c_64,c_58,c_56,c_1729])).

tff(c_1734,plain,(
    ! [D_468] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',u1_struct_0(D_468)) = k2_tmap_1('#skF_4','#skF_3','#skF_5',D_468)
      | ~ m1_pre_topc(D_468,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_68,c_1733])).

tff(c_1859,plain,
    ( k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1833,c_1734])).

tff(c_1866,plain,(
    k3_tmap_1('#skF_3','#skF_3','#skF_4','#skF_4','#skF_5') = k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1834,c_1859])).

tff(c_1874,plain,
    ( m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_22])).

tff(c_1887,plain,
    ( m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_66,c_64,c_60,c_60,c_58,c_56,c_54,c_1874])).

tff(c_1888,plain,(
    m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1887])).

tff(c_1714,plain,(
    ! [D_458,C_459,B_460,A_462,E_461] :
      ( v1_funct_1(k3_tmap_1(A_462,B_460,C_459,D_458,E_461))
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_459),u1_struct_0(B_460))))
      | ~ v1_funct_2(E_461,u1_struct_0(C_459),u1_struct_0(B_460))
      | ~ v1_funct_1(E_461)
      | ~ m1_pre_topc(D_458,A_462)
      | ~ m1_pre_topc(C_459,A_462)
      | ~ l1_pre_topc(B_460)
      | ~ v2_pre_topc(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1718,plain,(
    ! [A_462,D_458] :
      ( v1_funct_1(k3_tmap_1(A_462,'#skF_3','#skF_4',D_458,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_458,A_462)
      | ~ m1_pre_topc('#skF_4',A_462)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(resolution,[status(thm)],[c_54,c_1714])).

tff(c_1722,plain,(
    ! [A_462,D_458] :
      ( v1_funct_1(k3_tmap_1(A_462,'#skF_3','#skF_4',D_458,'#skF_5'))
      | ~ m1_pre_topc(D_458,A_462)
      | ~ m1_pre_topc('#skF_4',A_462)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1718])).

tff(c_1723,plain,(
    ! [A_462,D_458] :
      ( v1_funct_1(k3_tmap_1(A_462,'#skF_3','#skF_4',D_458,'#skF_5'))
      | ~ m1_pre_topc(D_458,A_462)
      | ~ m1_pre_topc('#skF_4',A_462)
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1722])).

tff(c_1883,plain,
    ( v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_1723])).

tff(c_1896,plain,
    ( v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_60,c_1883])).

tff(c_1897,plain,(
    v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1896])).

tff(c_1765,plain,(
    ! [A_487,C_484,B_485,D_483,E_486] :
      ( v1_funct_2(k3_tmap_1(A_487,B_485,C_484,D_483,E_486),u1_struct_0(D_483),u1_struct_0(B_485))
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_484),u1_struct_0(B_485))))
      | ~ v1_funct_2(E_486,u1_struct_0(C_484),u1_struct_0(B_485))
      | ~ v1_funct_1(E_486)
      | ~ m1_pre_topc(D_483,A_487)
      | ~ m1_pre_topc(C_484,A_487)
      | ~ l1_pre_topc(B_485)
      | ~ v2_pre_topc(B_485)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1769,plain,(
    ! [A_487,D_483] :
      ( v1_funct_2(k3_tmap_1(A_487,'#skF_3','#skF_4',D_483,'#skF_5'),u1_struct_0(D_483),u1_struct_0('#skF_3'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_483,A_487)
      | ~ m1_pre_topc('#skF_4',A_487)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(resolution,[status(thm)],[c_54,c_1765])).

tff(c_1773,plain,(
    ! [A_487,D_483] :
      ( v1_funct_2(k3_tmap_1(A_487,'#skF_3','#skF_4',D_483,'#skF_5'),u1_struct_0(D_483),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_483,A_487)
      | ~ m1_pre_topc('#skF_4',A_487)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1769])).

tff(c_1774,plain,(
    ! [A_487,D_483] :
      ( v1_funct_2(k3_tmap_1(A_487,'#skF_3','#skF_4',D_483,'#skF_5'),u1_struct_0(D_483),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(D_483,A_487)
      | ~ m1_pre_topc('#skF_4',A_487)
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1773])).

tff(c_1877,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_1774])).

tff(c_1890,plain,
    ( v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_60,c_1877])).

tff(c_1891,plain,(
    v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1890])).

tff(c_1749,plain,(
    ! [C_478,B_479,D_480,A_481] :
      ( r2_funct_2(u1_struct_0(C_478),u1_struct_0(B_479),D_480,k3_tmap_1(A_481,B_479,C_478,C_478,D_480))
      | ~ m1_subset_1(D_480,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_478),u1_struct_0(B_479))))
      | ~ v1_funct_2(D_480,u1_struct_0(C_478),u1_struct_0(B_479))
      | ~ v1_funct_1(D_480)
      | ~ m1_pre_topc(C_478,A_481)
      | v2_struct_0(C_478)
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1753,plain,(
    ! [A_481] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_481,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_481)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(resolution,[status(thm)],[c_54,c_1749])).

tff(c_1757,plain,(
    ! [A_481] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_481,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_481)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_56,c_1753])).

tff(c_1758,plain,(
    ! [A_481] :
      ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k3_tmap_1(A_481,'#skF_3','#skF_4','#skF_4','#skF_5'))
      | ~ m1_pre_topc('#skF_4',A_481)
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_1757])).

tff(c_1880,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1866,c_1758])).

tff(c_1893,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1880])).

tff(c_1894,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1893])).

tff(c_1914,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1894,c_12])).

tff(c_1917,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1897,c_1891,c_1914])).

tff(c_2028,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1888,c_1917])).

tff(c_1900,plain,(
    ! [A_507,B_510,E_508,C_506,D_509] :
      ( r2_hidden('#skF_2'(C_506,A_507,E_508,D_509,B_510),u1_struct_0(C_506))
      | r2_funct_2(u1_struct_0(C_506),u1_struct_0(A_507),k2_tmap_1(B_510,A_507,D_509,C_506),E_508)
      | ~ m1_subset_1(E_508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_506),u1_struct_0(A_507))))
      | ~ v1_funct_2(E_508,u1_struct_0(C_506),u1_struct_0(A_507))
      | ~ v1_funct_1(E_508)
      | ~ m1_subset_1(D_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_510),u1_struct_0(A_507))))
      | ~ v1_funct_2(D_509,u1_struct_0(B_510),u1_struct_0(A_507))
      | ~ v1_funct_1(D_509)
      | ~ m1_pre_topc(C_506,B_510)
      | v2_struct_0(C_506)
      | ~ l1_pre_topc(B_510)
      | ~ v2_pre_topc(B_510)
      | v2_struct_0(B_510)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_3199,plain,(
    ! [B_628,A_629,D_630,B_631] :
      ( r2_hidden('#skF_2'(B_628,A_629,k4_tmap_1(A_629,B_628),D_630,B_631),u1_struct_0(B_628))
      | r2_funct_2(u1_struct_0(B_628),u1_struct_0(A_629),k2_tmap_1(B_631,A_629,D_630,B_628),k4_tmap_1(A_629,B_628))
      | ~ v1_funct_2(k4_tmap_1(A_629,B_628),u1_struct_0(B_628),u1_struct_0(A_629))
      | ~ v1_funct_1(k4_tmap_1(A_629,B_628))
      | ~ m1_subset_1(D_630,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_631),u1_struct_0(A_629))))
      | ~ v1_funct_2(D_630,u1_struct_0(B_631),u1_struct_0(A_629))
      | ~ v1_funct_1(D_630)
      | ~ m1_pre_topc(B_628,B_631)
      | v2_struct_0(B_628)
      | ~ l1_pre_topc(B_631)
      | ~ v2_pre_topc(B_631)
      | v2_struct_0(B_631)
      | ~ m1_pre_topc(B_628,A_629)
      | ~ l1_pre_topc(A_629)
      | ~ v2_pre_topc(A_629)
      | v2_struct_0(A_629) ) ),
    inference(resolution,[status(thm)],[c_28,c_1900])).

tff(c_3204,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2028,c_3199])).

tff(c_3207,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_97,c_86,c_1834,c_58,c_56,c_54,c_3204])).

tff(c_3208,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_3207])).

tff(c_3209,plain,(
    ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3208])).

tff(c_3212,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_3209])).

tff(c_3215,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_3212])).

tff(c_3217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3215])).

tff(c_3219,plain,(
    v1_funct_1(k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3208])).

tff(c_3218,plain,
    ( ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3208])).

tff(c_3238,plain,(
    ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3218])).

tff(c_3241,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_3238])).

tff(c_3244,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_3241])).

tff(c_3246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3244])).

tff(c_3248,plain,(
    v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3218])).

tff(c_3247,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4'))
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3218])).

tff(c_3249,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3247])).

tff(c_3251,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_3249,c_12])).

tff(c_3254,plain,
    ( k4_tmap_1('#skF_3','#skF_4') = '#skF_5'
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_3219,c_3248,c_3251])).

tff(c_3268,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_3254])).

tff(c_3271,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_3268])).

tff(c_3274,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_3271])).

tff(c_3276,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3274])).

tff(c_3277,plain,(
    k4_tmap_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3254])).

tff(c_3282,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3277,c_50])).

tff(c_3288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_3282])).

tff(c_3289,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3247])).

tff(c_3316,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3289,c_2])).

tff(c_3325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1680,c_3316])).

tff(c_3327,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1678])).

tff(c_4769,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4728])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] :
      ( k3_funct_2(A_8,B_9,C_10,D_11) = k1_funct_1(C_10,D_11)
      | ~ m1_subset_1(D_11,A_8)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9)))
      | ~ v1_funct_2(C_10,A_8,B_9)
      | ~ v1_funct_1(C_10)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4782,plain,(
    ! [B_9,C_10] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_9,C_10,'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = k1_funct_1(C_10,'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_9)))
      | ~ v1_funct_2(C_10,u1_struct_0('#skF_4'),B_9)
      | ~ v1_funct_1(C_10)
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4769,c_8])).

tff(c_4786,plain,(
    ! [B_842,C_843] :
      ( k3_funct_2(u1_struct_0('#skF_4'),B_842,C_843,'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = k1_funct_1(C_843,'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'))
      | ~ m1_subset_1(C_843,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),B_842)))
      | ~ v1_funct_2(C_843,u1_struct_0('#skF_4'),B_842)
      | ~ v1_funct_1(C_843) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3327,c_4782])).

tff(c_4790,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = k1_funct_1(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'))
    | ~ v1_funct_2(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k3_tmap_1('#skF_4','#skF_3','#skF_4','#skF_4','#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3781,c_4786])).

tff(c_4812,plain,
    ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_97,c_3630,c_58,c_3518,c_56,c_3518,c_3518,c_3518,c_4790])).

tff(c_4813,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = k1_funct_1('#skF_5','#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4812])).

tff(c_4882,plain,(
    k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5','#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4876,c_4813])).

tff(c_38,plain,(
    ! [B_111,C_127,D_135,E_139,A_79] :
      ( k3_funct_2(u1_struct_0(B_111),u1_struct_0(A_79),D_135,'#skF_2'(C_127,A_79,E_139,D_135,B_111)) != k1_funct_1(E_139,'#skF_2'(C_127,A_79,E_139,D_135,B_111))
      | r2_funct_2(u1_struct_0(C_127),u1_struct_0(A_79),k2_tmap_1(B_111,A_79,D_135,C_127),E_139)
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127),u1_struct_0(A_79))))
      | ~ v1_funct_2(E_139,u1_struct_0(C_127),u1_struct_0(A_79))
      | ~ v1_funct_1(E_139)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_111),u1_struct_0(A_79))))
      | ~ v1_funct_2(D_135,u1_struct_0(B_111),u1_struct_0(A_79))
      | ~ v1_funct_1(D_135)
      | ~ m1_pre_topc(C_127,B_111)
      | v2_struct_0(C_127)
      | ~ l1_pre_topc(B_111)
      | ~ v2_pre_topc(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_79)
      | ~ v2_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_4889,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) != '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_4','#skF_3','#skF_5','#skF_4'),k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2(k4_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4882,c_38])).

tff(c_4893,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) != '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_5',k4_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_97,c_86,c_3630,c_58,c_56,c_54,c_4702,c_4729,c_3669,c_4889])).

tff(c_4894,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) != '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
    | ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_4770,c_4893])).

tff(c_4936,plain,(
    ~ m1_subset_1(k4_tmap_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_4894])).

tff(c_4939,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_4936])).

tff(c_4942,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_4939])).

tff(c_4944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4942])).

tff(c_4945,plain,(
    k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) != '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_4894])).

tff(c_4877,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_4861])).

tff(c_48,plain,(
    ! [A_163,B_167,C_169] :
      ( k1_funct_1(k4_tmap_1(A_163,B_167),C_169) = C_169
      | ~ r2_hidden(C_169,u1_struct_0(B_167))
      | ~ m1_subset_1(C_169,u1_struct_0(A_163))
      | ~ m1_pre_topc(B_167,A_163)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_303])).

tff(c_4848,plain,(
    ! [A_163] :
      ( k1_funct_1(k4_tmap_1(A_163,'#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0(A_163))
      | ~ m1_pre_topc('#skF_4',A_163)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_4846,c_48])).

tff(c_13047,plain,(
    ! [A_1200] :
      ( k1_funct_1(k4_tmap_1(A_1200,'#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4'),u1_struct_0(A_1200))
      | ~ m1_pre_topc('#skF_4',A_1200)
      | ~ l1_pre_topc(A_1200)
      | ~ v2_pre_topc(A_1200)
      | v2_struct_0(A_1200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4848])).

tff(c_13050,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4877,c_13047])).

tff(c_13061,plain,
    ( k1_funct_1(k4_tmap_1('#skF_3','#skF_4'),'#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')) = '#skF_2'('#skF_4','#skF_3',k4_tmap_1('#skF_3','#skF_4'),'#skF_5','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_13050])).

tff(c_13063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4945,c_13061])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.03/4.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.19/4.76  
% 12.19/4.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.19/4.77  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k4_tmap_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 12.19/4.77  
% 12.19/4.77  %Foreground sorts:
% 12.19/4.77  
% 12.19/4.77  
% 12.19/4.77  %Background operators:
% 12.19/4.77  
% 12.19/4.77  
% 12.19/4.77  %Foreground operators:
% 12.19/4.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.19/4.77  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 12.19/4.77  tff(k4_tmap_1, type, k4_tmap_1: ($i * $i) > $i).
% 12.19/4.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.19/4.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.19/4.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.19/4.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 12.19/4.77  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.19/4.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.19/4.77  tff('#skF_5', type, '#skF_5': $i).
% 12.19/4.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.19/4.77  tff('#skF_3', type, '#skF_3': $i).
% 12.19/4.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.19/4.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.19/4.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.19/4.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.19/4.77  tff('#skF_4', type, '#skF_4': $i).
% 12.19/4.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.19/4.77  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 12.19/4.77  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 12.19/4.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.19/4.77  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 12.19/4.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.19/4.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.19/4.77  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 12.19/4.77  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 12.19/4.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.19/4.77  
% 12.19/4.81  tff(f_333, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, u1_struct_0(B)) => (D = k1_funct_1(C, D))))) => r2_funct_2(u1_struct_0(B), u1_struct_0(A), k4_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_tmap_1)).
% 12.19/4.81  tff(f_186, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_funct_1(k4_tmap_1(A, B)) & v1_funct_2(k4_tmap_1(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(k4_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 12.19/4.81  tff(f_66, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 12.19/4.81  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 12.19/4.81  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 12.19/4.81  tff(f_197, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 12.19/4.81  tff(f_171, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 12.19/4.81  tff(f_271, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(B), D, k3_tmap_1(A, B, C, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 12.19/4.81  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 12.19/4.81  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 12.19/4.81  tff(f_241, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 12.19/4.81  tff(f_193, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 12.19/4.81  tff(f_37, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 12.19/4.81  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 12.19/4.81  tff(f_303, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, u1_struct_0(B)) => (k1_funct_1(k4_tmap_1(A, B), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_tmap_1)).
% 12.19/4.81  tff(f_50, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 12.19/4.81  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_28, plain, (![A_73, B_74]: (m1_subset_1(k4_tmap_1(A_73, B_74), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_74), u1_struct_0(A_73)))) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.19/4.81  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_136, plain, (![A_210, B_211, D_212]: (r2_funct_2(A_210, B_211, D_212, D_212) | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~v1_funct_2(D_212, A_210, B_211) | ~v1_funct_1(D_212))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.19/4.81  tff(c_138, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_54, c_136])).
% 12.19/4.81  tff(c_141, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_138])).
% 12.19/4.81  tff(c_32, plain, (![A_73, B_74]: (v1_funct_1(k4_tmap_1(A_73, B_74)) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.19/4.81  tff(c_87, plain, (![B_188, A_189]: (v2_pre_topc(B_188) | ~m1_pre_topc(B_188, A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_75])).
% 12.19/4.81  tff(c_93, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_87])).
% 12.19/4.81  tff(c_97, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_93])).
% 12.19/4.81  tff(c_76, plain, (![B_186, A_187]: (l1_pre_topc(B_186) | ~m1_pre_topc(B_186, A_187) | ~l1_pre_topc(A_187))), inference(cnfTransformation, [status(thm)], [f_82])).
% 12.19/4.81  tff(c_82, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_60, c_76])).
% 12.19/4.81  tff(c_86, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_82])).
% 12.19/4.81  tff(c_36, plain, (![A_78]: (m1_pre_topc(A_78, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_197])).
% 12.19/4.81  tff(c_3389, plain, (![C_658, A_661, B_659, D_657, E_660]: (v1_funct_1(k3_tmap_1(A_661, B_659, C_658, D_657, E_660)) | ~m1_subset_1(E_660, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_658), u1_struct_0(B_659)))) | ~v1_funct_2(E_660, u1_struct_0(C_658), u1_struct_0(B_659)) | ~v1_funct_1(E_660) | ~m1_pre_topc(D_657, A_661) | ~m1_pre_topc(C_658, A_661) | ~l1_pre_topc(B_659) | ~v2_pre_topc(B_659) | v2_struct_0(B_659) | ~l1_pre_topc(A_661) | ~v2_pre_topc(A_661) | v2_struct_0(A_661))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.19/4.81  tff(c_3393, plain, (![A_661, D_657]: (v1_funct_1(k3_tmap_1(A_661, '#skF_3', '#skF_4', D_657, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_657, A_661) | ~m1_pre_topc('#skF_4', A_661) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_661) | ~v2_pre_topc(A_661) | v2_struct_0(A_661))), inference(resolution, [status(thm)], [c_54, c_3389])).
% 12.19/4.81  tff(c_3397, plain, (![A_661, D_657]: (v1_funct_1(k3_tmap_1(A_661, '#skF_3', '#skF_4', D_657, '#skF_5')) | ~m1_pre_topc(D_657, A_661) | ~m1_pre_topc('#skF_4', A_661) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_661) | ~v2_pre_topc(A_661) | v2_struct_0(A_661))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_3393])).
% 12.19/4.81  tff(c_3398, plain, (![A_661, D_657]: (v1_funct_1(k3_tmap_1(A_661, '#skF_3', '#skF_4', D_657, '#skF_5')) | ~m1_pre_topc(D_657, A_661) | ~m1_pre_topc('#skF_4', A_661) | ~l1_pre_topc(A_661) | ~v2_pre_topc(A_661) | v2_struct_0(A_661))), inference(negUnitSimplification, [status(thm)], [c_68, c_3397])).
% 12.19/4.81  tff(c_3440, plain, (![A_686, B_684, E_685, C_683, D_682]: (v1_funct_2(k3_tmap_1(A_686, B_684, C_683, D_682, E_685), u1_struct_0(D_682), u1_struct_0(B_684)) | ~m1_subset_1(E_685, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_683), u1_struct_0(B_684)))) | ~v1_funct_2(E_685, u1_struct_0(C_683), u1_struct_0(B_684)) | ~v1_funct_1(E_685) | ~m1_pre_topc(D_682, A_686) | ~m1_pre_topc(C_683, A_686) | ~l1_pre_topc(B_684) | ~v2_pre_topc(B_684) | v2_struct_0(B_684) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.19/4.81  tff(c_3444, plain, (![A_686, D_682]: (v1_funct_2(k3_tmap_1(A_686, '#skF_3', '#skF_4', D_682, '#skF_5'), u1_struct_0(D_682), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_682, A_686) | ~m1_pre_topc('#skF_4', A_686) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(resolution, [status(thm)], [c_54, c_3440])).
% 12.19/4.81  tff(c_3448, plain, (![A_686, D_682]: (v1_funct_2(k3_tmap_1(A_686, '#skF_3', '#skF_4', D_682, '#skF_5'), u1_struct_0(D_682), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_682, A_686) | ~m1_pre_topc('#skF_4', A_686) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_3444])).
% 12.19/4.81  tff(c_3449, plain, (![A_686, D_682]: (v1_funct_2(k3_tmap_1(A_686, '#skF_3', '#skF_4', D_682, '#skF_5'), u1_struct_0(D_682), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_682, A_686) | ~m1_pre_topc('#skF_4', A_686) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(negUnitSimplification, [status(thm)], [c_68, c_3448])).
% 12.19/4.81  tff(c_22, plain, (![E_72, C_70, B_69, D_71, A_68]: (m1_subset_1(k3_tmap_1(A_68, B_69, C_70, D_71, E_72), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_71), u1_struct_0(B_69)))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_70), u1_struct_0(B_69)))) | ~v1_funct_2(E_72, u1_struct_0(C_70), u1_struct_0(B_69)) | ~v1_funct_1(E_72) | ~m1_pre_topc(D_71, A_68) | ~m1_pre_topc(C_70, A_68) | ~l1_pre_topc(B_69) | ~v2_pre_topc(B_69) | v2_struct_0(B_69) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.19/4.81  tff(c_3423, plain, (![C_673, B_674, D_675, A_676]: (r2_funct_2(u1_struct_0(C_673), u1_struct_0(B_674), D_675, k3_tmap_1(A_676, B_674, C_673, C_673, D_675)) | ~m1_subset_1(D_675, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_673), u1_struct_0(B_674)))) | ~v1_funct_2(D_675, u1_struct_0(C_673), u1_struct_0(B_674)) | ~v1_funct_1(D_675) | ~m1_pre_topc(C_673, A_676) | v2_struct_0(C_673) | ~l1_pre_topc(B_674) | ~v2_pre_topc(B_674) | v2_struct_0(B_674) | ~l1_pre_topc(A_676) | ~v2_pre_topc(A_676) | v2_struct_0(A_676))), inference(cnfTransformation, [status(thm)], [f_271])).
% 12.19/4.81  tff(c_3427, plain, (![A_676]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_676, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_676) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_676) | ~v2_pre_topc(A_676) | v2_struct_0(A_676))), inference(resolution, [status(thm)], [c_54, c_3423])).
% 12.19/4.81  tff(c_3431, plain, (![A_676]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_676, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_676) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_676) | ~v2_pre_topc(A_676) | v2_struct_0(A_676))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_3427])).
% 12.19/4.81  tff(c_3433, plain, (![A_677]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_677, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_677) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_3431])).
% 12.19/4.81  tff(c_12, plain, (![D_15, C_14, A_12, B_13]: (D_15=C_14 | ~r2_funct_2(A_12, B_13, C_14, D_15) | ~m1_subset_1(D_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_2(D_15, A_12, B_13) | ~v1_funct_1(D_15) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | ~v1_funct_2(C_14, A_12, B_13) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.19/4.81  tff(c_3435, plain, (![A_677]: (k3_tmap_1(A_677, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_677, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_677, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_677, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_677) | ~l1_pre_topc(A_677) | ~v2_pre_topc(A_677) | v2_struct_0(A_677))), inference(resolution, [status(thm)], [c_3433, c_12])).
% 12.19/4.81  tff(c_3486, plain, (![A_701]: (k3_tmap_1(A_701, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_701, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_701, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_701, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_701) | ~l1_pre_topc(A_701) | ~v2_pre_topc(A_701) | v2_struct_0(A_701))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_3435])).
% 12.19/4.81  tff(c_3490, plain, (![A_68]: (k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_68) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_22, c_3486])).
% 12.19/4.81  tff(c_3493, plain, (![A_68]: (k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_68) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_3490])).
% 12.19/4.81  tff(c_3495, plain, (![A_702]: (k3_tmap_1(A_702, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_702, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_702, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_702) | ~l1_pre_topc(A_702) | ~v2_pre_topc(A_702) | v2_struct_0(A_702))), inference(negUnitSimplification, [status(thm)], [c_68, c_3493])).
% 12.19/4.81  tff(c_3501, plain, (![A_703]: (k3_tmap_1(A_703, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_1(k3_tmap_1(A_703, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_703) | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703) | v2_struct_0(A_703))), inference(resolution, [status(thm)], [c_3449, c_3495])).
% 12.19/4.81  tff(c_3507, plain, (![A_704]: (k3_tmap_1(A_704, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_pre_topc('#skF_4', A_704) | ~l1_pre_topc(A_704) | ~v2_pre_topc(A_704) | v2_struct_0(A_704))), inference(resolution, [status(thm)], [c_3398, c_3501])).
% 12.19/4.81  tff(c_3514, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3507])).
% 12.19/4.81  tff(c_3521, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3514])).
% 12.19/4.81  tff(c_3522, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_68, c_3521])).
% 12.19/4.81  tff(c_3598, plain, (![A_716, B_717, C_715, D_718, E_714]: (k3_tmap_1(A_716, B_717, C_715, D_718, E_714)=k2_partfun1(u1_struct_0(C_715), u1_struct_0(B_717), E_714, u1_struct_0(D_718)) | ~m1_pre_topc(D_718, C_715) | ~m1_subset_1(E_714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_715), u1_struct_0(B_717)))) | ~v1_funct_2(E_714, u1_struct_0(C_715), u1_struct_0(B_717)) | ~v1_funct_1(E_714) | ~m1_pre_topc(D_718, A_716) | ~m1_pre_topc(C_715, A_716) | ~l1_pre_topc(B_717) | ~v2_pre_topc(B_717) | v2_struct_0(B_717) | ~l1_pre_topc(A_716) | ~v2_pre_topc(A_716) | v2_struct_0(A_716))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.19/4.81  tff(c_3604, plain, (![A_716, D_718]: (k3_tmap_1(A_716, '#skF_3', '#skF_4', D_718, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_718)) | ~m1_pre_topc(D_718, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_718, A_716) | ~m1_pre_topc('#skF_4', A_716) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_716) | ~v2_pre_topc(A_716) | v2_struct_0(A_716))), inference(resolution, [status(thm)], [c_54, c_3598])).
% 12.19/4.81  tff(c_3609, plain, (![A_716, D_718]: (k3_tmap_1(A_716, '#skF_3', '#skF_4', D_718, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_718)) | ~m1_pre_topc(D_718, '#skF_4') | ~m1_pre_topc(D_718, A_716) | ~m1_pre_topc('#skF_4', A_716) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_716) | ~v2_pre_topc(A_716) | v2_struct_0(A_716))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_3604])).
% 12.19/4.81  tff(c_3611, plain, (![A_719, D_720]: (k3_tmap_1(A_719, '#skF_3', '#skF_4', D_720, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_720)) | ~m1_pre_topc(D_720, '#skF_4') | ~m1_pre_topc(D_720, A_719) | ~m1_pre_topc('#skF_4', A_719) | ~l1_pre_topc(A_719) | ~v2_pre_topc(A_719) | v2_struct_0(A_719))), inference(negUnitSimplification, [status(thm)], [c_68, c_3609])).
% 12.19/4.81  tff(c_3615, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_3611])).
% 12.19/4.81  tff(c_3619, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_3522, c_3615])).
% 12.19/4.81  tff(c_3620, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_3619])).
% 12.19/4.81  tff(c_3621, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_3620])).
% 12.19/4.81  tff(c_3624, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3621])).
% 12.19/4.81  tff(c_3628, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_3624])).
% 12.19/4.81  tff(c_3630, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_3620])).
% 12.19/4.81  tff(c_3629, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_3620])).
% 12.19/4.81  tff(c_3399, plain, (![A_662, B_663, C_664, D_665]: (k2_partfun1(u1_struct_0(A_662), u1_struct_0(B_663), C_664, u1_struct_0(D_665))=k2_tmap_1(A_662, B_663, C_664, D_665) | ~m1_pre_topc(D_665, A_662) | ~m1_subset_1(C_664, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_662), u1_struct_0(B_663)))) | ~v1_funct_2(C_664, u1_struct_0(A_662), u1_struct_0(B_663)) | ~v1_funct_1(C_664) | ~l1_pre_topc(B_663) | ~v2_pre_topc(B_663) | v2_struct_0(B_663) | ~l1_pre_topc(A_662) | ~v2_pre_topc(A_662) | v2_struct_0(A_662))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.19/4.81  tff(c_3403, plain, (![D_665]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_665))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_665) | ~m1_pre_topc(D_665, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_3399])).
% 12.19/4.81  tff(c_3407, plain, (![D_665]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_665))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_665) | ~m1_pre_topc(D_665, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_86, c_66, c_64, c_58, c_56, c_3403])).
% 12.19/4.81  tff(c_3408, plain, (![D_665]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_665))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_665) | ~m1_pre_topc(D_665, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_3407])).
% 12.19/4.81  tff(c_3662, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3629, c_3408])).
% 12.19/4.81  tff(c_3669, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3630, c_3662])).
% 12.19/4.81  tff(c_3731, plain, (![A_723, C_722, B_726, D_725, E_724]: (m1_subset_1('#skF_2'(C_722, A_723, E_724, D_725, B_726), u1_struct_0(B_726)) | r2_funct_2(u1_struct_0(C_722), u1_struct_0(A_723), k2_tmap_1(B_726, A_723, D_725, C_722), E_724) | ~m1_subset_1(E_724, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_722), u1_struct_0(A_723)))) | ~v1_funct_2(E_724, u1_struct_0(C_722), u1_struct_0(A_723)) | ~v1_funct_1(E_724) | ~m1_subset_1(D_725, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_726), u1_struct_0(A_723)))) | ~v1_funct_2(D_725, u1_struct_0(B_726), u1_struct_0(A_723)) | ~v1_funct_1(D_725) | ~m1_pre_topc(C_722, B_726) | v2_struct_0(C_722) | ~l1_pre_topc(B_726) | ~v2_pre_topc(B_726) | v2_struct_0(B_726) | ~l1_pre_topc(A_723) | ~v2_pre_topc(A_723) | v2_struct_0(A_723))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.19/4.81  tff(c_4679, plain, (![B_829, A_830, D_831, B_832]: (m1_subset_1('#skF_2'(B_829, A_830, k4_tmap_1(A_830, B_829), D_831, B_832), u1_struct_0(B_832)) | r2_funct_2(u1_struct_0(B_829), u1_struct_0(A_830), k2_tmap_1(B_832, A_830, D_831, B_829), k4_tmap_1(A_830, B_829)) | ~v1_funct_2(k4_tmap_1(A_830, B_829), u1_struct_0(B_829), u1_struct_0(A_830)) | ~v1_funct_1(k4_tmap_1(A_830, B_829)) | ~m1_subset_1(D_831, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_832), u1_struct_0(A_830)))) | ~v1_funct_2(D_831, u1_struct_0(B_832), u1_struct_0(A_830)) | ~v1_funct_1(D_831) | ~m1_pre_topc(B_829, B_832) | v2_struct_0(B_829) | ~l1_pre_topc(B_832) | ~v2_pre_topc(B_832) | v2_struct_0(B_832) | ~m1_pre_topc(B_829, A_830) | ~l1_pre_topc(A_830) | ~v2_pre_topc(A_830) | v2_struct_0(A_830))), inference(resolution, [status(thm)], [c_28, c_3731])).
% 12.19/4.81  tff(c_4686, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3669, c_4679])).
% 12.19/4.81  tff(c_4690, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_97, c_86, c_3630, c_58, c_56, c_54, c_4686])).
% 12.19/4.81  tff(c_4691, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_4690])).
% 12.19/4.81  tff(c_4692, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4691])).
% 12.19/4.81  tff(c_4695, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_4692])).
% 12.19/4.81  tff(c_4698, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_4695])).
% 12.19/4.81  tff(c_4700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_4698])).
% 12.19/4.81  tff(c_4702, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_4691])).
% 12.19/4.81  tff(c_30, plain, (![A_73, B_74]: (v1_funct_2(k4_tmap_1(A_73, B_74), u1_struct_0(B_74), u1_struct_0(A_73)) | ~m1_pre_topc(B_74, A_73) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_186])).
% 12.19/4.81  tff(c_4701, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_4691])).
% 12.19/4.81  tff(c_4719, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_4701])).
% 12.19/4.81  tff(c_4722, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_4719])).
% 12.19/4.81  tff(c_4725, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_4722])).
% 12.19/4.81  tff(c_4727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_4725])).
% 12.19/4.81  tff(c_4729, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_4701])).
% 12.19/4.81  tff(c_4728, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_4701])).
% 12.19/4.81  tff(c_4730, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_4728])).
% 12.19/4.81  tff(c_4732, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_4730, c_12])).
% 12.19/4.81  tff(c_4735, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_4702, c_4729, c_4732])).
% 12.19/4.81  tff(c_4746, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_4735])).
% 12.19/4.81  tff(c_4749, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_4746])).
% 12.19/4.81  tff(c_4752, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_4749])).
% 12.19/4.81  tff(c_4754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_4752])).
% 12.19/4.81  tff(c_4755, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_4735])).
% 12.19/4.81  tff(c_50, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k4_tmap_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_4761, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4755, c_50])).
% 12.19/4.81  tff(c_4768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_4761])).
% 12.19/4.81  tff(c_4770, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_4728])).
% 12.19/4.81  tff(c_3902, plain, (![A_737, B_740, D_739, C_736, E_738]: (r2_hidden('#skF_2'(C_736, A_737, E_738, D_739, B_740), u1_struct_0(C_736)) | r2_funct_2(u1_struct_0(C_736), u1_struct_0(A_737), k2_tmap_1(B_740, A_737, D_739, C_736), E_738) | ~m1_subset_1(E_738, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_736), u1_struct_0(A_737)))) | ~v1_funct_2(E_738, u1_struct_0(C_736), u1_struct_0(A_737)) | ~v1_funct_1(E_738) | ~m1_subset_1(D_739, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_740), u1_struct_0(A_737)))) | ~v1_funct_2(D_739, u1_struct_0(B_740), u1_struct_0(A_737)) | ~v1_funct_1(D_739) | ~m1_pre_topc(C_736, B_740) | v2_struct_0(C_736) | ~l1_pre_topc(B_740) | ~v2_pre_topc(B_740) | v2_struct_0(B_740) | ~l1_pre_topc(A_737) | ~v2_pre_topc(A_737) | v2_struct_0(A_737))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.19/4.81  tff(c_4837, plain, (![B_844, A_845, D_846, B_847]: (r2_hidden('#skF_2'(B_844, A_845, k4_tmap_1(A_845, B_844), D_846, B_847), u1_struct_0(B_844)) | r2_funct_2(u1_struct_0(B_844), u1_struct_0(A_845), k2_tmap_1(B_847, A_845, D_846, B_844), k4_tmap_1(A_845, B_844)) | ~v1_funct_2(k4_tmap_1(A_845, B_844), u1_struct_0(B_844), u1_struct_0(A_845)) | ~v1_funct_1(k4_tmap_1(A_845, B_844)) | ~m1_subset_1(D_846, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_847), u1_struct_0(A_845)))) | ~v1_funct_2(D_846, u1_struct_0(B_847), u1_struct_0(A_845)) | ~v1_funct_1(D_846) | ~m1_pre_topc(B_844, B_847) | v2_struct_0(B_844) | ~l1_pre_topc(B_847) | ~v2_pre_topc(B_847) | v2_struct_0(B_847) | ~m1_pre_topc(B_844, A_845) | ~l1_pre_topc(A_845) | ~v2_pre_topc(A_845) | v2_struct_0(A_845))), inference(resolution, [status(thm)], [c_28, c_3902])).
% 12.19/4.81  tff(c_4842, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3669, c_4837])).
% 12.19/4.81  tff(c_4845, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_97, c_86, c_3630, c_58, c_56, c_54, c_4702, c_4729, c_4842])).
% 12.19/4.81  tff(c_4846, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_4770, c_4845])).
% 12.19/4.81  tff(c_103, plain, (![B_194, A_195]: (m1_subset_1(u1_struct_0(B_194), k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_pre_topc(B_194, A_195) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_193])).
% 12.19/4.81  tff(c_6, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.19/4.81  tff(c_106, plain, (![A_5, A_195, B_194]: (m1_subset_1(A_5, u1_struct_0(A_195)) | ~r2_hidden(A_5, u1_struct_0(B_194)) | ~m1_pre_topc(B_194, A_195) | ~l1_pre_topc(A_195))), inference(resolution, [status(thm)], [c_103, c_6])).
% 12.19/4.81  tff(c_4860, plain, (![A_195]: (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0(A_195)) | ~m1_pre_topc('#skF_4', A_195) | ~l1_pre_topc(A_195))), inference(resolution, [status(thm)], [c_4846, c_106])).
% 12.19/4.81  tff(c_52, plain, (![D_181]: (k1_funct_1('#skF_5', D_181)=D_181 | ~r2_hidden(D_181, u1_struct_0('#skF_4')) | ~m1_subset_1(D_181, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_4861, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4846, c_52])).
% 12.19/4.81  tff(c_4868, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_4861])).
% 12.19/4.81  tff(c_4871, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4860, c_4868])).
% 12.19/4.81  tff(c_4875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_4871])).
% 12.19/4.81  tff(c_4876, plain, (k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_4861])).
% 12.19/4.81  tff(c_3511, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3507])).
% 12.19/4.81  tff(c_3517, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_97, c_3511])).
% 12.19/4.81  tff(c_3518, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_3517])).
% 12.19/4.81  tff(c_3616, plain, (![A_78]: (k3_tmap_1(A_78, '#skF_3', '#skF_4', A_78, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_78)) | ~m1_pre_topc(A_78, '#skF_4') | ~m1_pre_topc('#skF_4', A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_36, c_3611])).
% 12.19/4.81  tff(c_3679, plain, (![A_721]: (k3_tmap_1(A_721, '#skF_3', '#skF_4', A_721, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_721)) | ~m1_pre_topc(A_721, '#skF_4') | ~m1_pre_topc('#skF_4', A_721) | ~v2_pre_topc(A_721) | v2_struct_0(A_721) | ~l1_pre_topc(A_721))), inference(resolution, [status(thm)], [c_36, c_3611])).
% 12.19/4.81  tff(c_3693, plain, (![A_721]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_721)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_721), u1_struct_0('#skF_3')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(A_721, A_721) | ~m1_pre_topc('#skF_4', A_721) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_721) | ~v2_pre_topc(A_721) | v2_struct_0(A_721) | ~m1_pre_topc(A_721, '#skF_4') | ~m1_pre_topc('#skF_4', A_721) | ~v2_pre_topc(A_721) | v2_struct_0(A_721) | ~l1_pre_topc(A_721))), inference(superposition, [status(thm), theory('equality')], [c_3679, c_22])).
% 12.19/4.81  tff(c_3724, plain, (![A_721]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_721)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_721), u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_721, A_721) | v2_struct_0('#skF_3') | ~m1_pre_topc(A_721, '#skF_4') | ~m1_pre_topc('#skF_4', A_721) | ~v2_pre_topc(A_721) | v2_struct_0(A_721) | ~l1_pre_topc(A_721))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_3693])).
% 12.19/4.81  tff(c_3758, plain, (![A_728]: (m1_subset_1(k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(A_728)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_728), u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_728, A_728) | ~m1_pre_topc(A_728, '#skF_4') | ~m1_pre_topc('#skF_4', A_728) | ~v2_pre_topc(A_728) | v2_struct_0(A_728) | ~l1_pre_topc(A_728))), inference(negUnitSimplification, [status(thm)], [c_68, c_3724])).
% 12.19/4.81  tff(c_3781, plain, (![A_78]: (m1_subset_1(k3_tmap_1(A_78, '#skF_3', '#skF_4', A_78, '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_78), u1_struct_0('#skF_3')))) | ~m1_pre_topc(A_78, A_78) | ~m1_pre_topc(A_78, '#skF_4') | ~m1_pre_topc('#skF_4', A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~l1_pre_topc(A_78) | ~m1_pre_topc(A_78, '#skF_4') | ~m1_pre_topc('#skF_4', A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78) | ~l1_pre_topc(A_78))), inference(superposition, [status(thm), theory('equality')], [c_3616, c_3758])).
% 12.19/4.81  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.19/4.81  tff(c_129, plain, (![A_203, A_204, B_205]: (m1_subset_1(A_203, u1_struct_0(A_204)) | ~r2_hidden(A_203, u1_struct_0(B_205)) | ~m1_pre_topc(B_205, A_204) | ~l1_pre_topc(A_204))), inference(resolution, [status(thm)], [c_103, c_6])).
% 12.19/4.81  tff(c_133, plain, (![B_205, A_204]: (m1_subset_1('#skF_1'(u1_struct_0(B_205)), u1_struct_0(A_204)) | ~m1_pre_topc(B_205, A_204) | ~l1_pre_topc(A_204) | v1_xboole_0(u1_struct_0(B_205)))), inference(resolution, [status(thm)], [c_4, c_129])).
% 12.19/4.81  tff(c_107, plain, (![D_196]: (k1_funct_1('#skF_5', D_196)=D_196 | ~r2_hidden(D_196, u1_struct_0('#skF_4')) | ~m1_subset_1(D_196, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_333])).
% 12.19/4.81  tff(c_112, plain, (k1_funct_1('#skF_5', '#skF_1'(u1_struct_0('#skF_4')))='#skF_1'(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(u1_struct_0('#skF_4')), u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_107])).
% 12.19/4.81  tff(c_142, plain, (~m1_subset_1('#skF_1'(u1_struct_0('#skF_4')), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_112])).
% 12.19/4.81  tff(c_145, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_133, c_142])).
% 12.19/4.81  tff(c_148, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_145])).
% 12.19/4.81  tff(c_217, plain, (![C_244, B_245, D_243, E_246, A_247]: (v1_funct_1(k3_tmap_1(A_247, B_245, C_244, D_243, E_246)) | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_244), u1_struct_0(B_245)))) | ~v1_funct_2(E_246, u1_struct_0(C_244), u1_struct_0(B_245)) | ~v1_funct_1(E_246) | ~m1_pre_topc(D_243, A_247) | ~m1_pre_topc(C_244, A_247) | ~l1_pre_topc(B_245) | ~v2_pre_topc(B_245) | v2_struct_0(B_245) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.19/4.81  tff(c_221, plain, (![A_247, D_243]: (v1_funct_1(k3_tmap_1(A_247, '#skF_3', '#skF_4', D_243, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_243, A_247) | ~m1_pre_topc('#skF_4', A_247) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(resolution, [status(thm)], [c_54, c_217])).
% 12.19/4.81  tff(c_225, plain, (![A_247, D_243]: (v1_funct_1(k3_tmap_1(A_247, '#skF_3', '#skF_4', D_243, '#skF_5')) | ~m1_pre_topc(D_243, A_247) | ~m1_pre_topc('#skF_4', A_247) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_221])).
% 12.19/4.81  tff(c_226, plain, (![A_247, D_243]: (v1_funct_1(k3_tmap_1(A_247, '#skF_3', '#skF_4', D_243, '#skF_5')) | ~m1_pre_topc(D_243, A_247) | ~m1_pre_topc('#skF_4', A_247) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247) | v2_struct_0(A_247))), inference(negUnitSimplification, [status(thm)], [c_68, c_225])).
% 12.19/4.81  tff(c_248, plain, (![C_256, D_255, E_258, A_259, B_257]: (v1_funct_2(k3_tmap_1(A_259, B_257, C_256, D_255, E_258), u1_struct_0(D_255), u1_struct_0(B_257)) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256), u1_struct_0(B_257)))) | ~v1_funct_2(E_258, u1_struct_0(C_256), u1_struct_0(B_257)) | ~v1_funct_1(E_258) | ~m1_pre_topc(D_255, A_259) | ~m1_pre_topc(C_256, A_259) | ~l1_pre_topc(B_257) | ~v2_pre_topc(B_257) | v2_struct_0(B_257) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.19/4.81  tff(c_252, plain, (![A_259, D_255]: (v1_funct_2(k3_tmap_1(A_259, '#skF_3', '#skF_4', D_255, '#skF_5'), u1_struct_0(D_255), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_255, A_259) | ~m1_pre_topc('#skF_4', A_259) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(resolution, [status(thm)], [c_54, c_248])).
% 12.19/4.81  tff(c_256, plain, (![A_259, D_255]: (v1_funct_2(k3_tmap_1(A_259, '#skF_3', '#skF_4', D_255, '#skF_5'), u1_struct_0(D_255), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_255, A_259) | ~m1_pre_topc('#skF_4', A_259) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_252])).
% 12.19/4.81  tff(c_257, plain, (![A_259, D_255]: (v1_funct_2(k3_tmap_1(A_259, '#skF_3', '#skF_4', D_255, '#skF_5'), u1_struct_0(D_255), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_255, A_259) | ~m1_pre_topc('#skF_4', A_259) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(negUnitSimplification, [status(thm)], [c_68, c_256])).
% 12.19/4.81  tff(c_264, plain, (![C_270, B_271, D_272, A_273]: (r2_funct_2(u1_struct_0(C_270), u1_struct_0(B_271), D_272, k3_tmap_1(A_273, B_271, C_270, C_270, D_272)) | ~m1_subset_1(D_272, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_270), u1_struct_0(B_271)))) | ~v1_funct_2(D_272, u1_struct_0(C_270), u1_struct_0(B_271)) | ~v1_funct_1(D_272) | ~m1_pre_topc(C_270, A_273) | v2_struct_0(C_270) | ~l1_pre_topc(B_271) | ~v2_pre_topc(B_271) | v2_struct_0(B_271) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_271])).
% 12.19/4.81  tff(c_268, plain, (![A_273]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_273, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_273) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_54, c_264])).
% 12.19/4.81  tff(c_272, plain, (![A_273]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_273, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_273) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_268])).
% 12.19/4.81  tff(c_274, plain, (![A_274]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_274, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_272])).
% 12.19/4.81  tff(c_276, plain, (![A_274]: (k3_tmap_1(A_274, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_274, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_274, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_274, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_274, c_12])).
% 12.19/4.81  tff(c_315, plain, (![A_287]: (k3_tmap_1(A_287, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_subset_1(k3_tmap_1(A_287, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k3_tmap_1(A_287, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_287, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_287) | ~l1_pre_topc(A_287) | ~v2_pre_topc(A_287) | v2_struct_0(A_287))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_276])).
% 12.19/4.81  tff(c_319, plain, (![A_68]: (k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_68) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_22, c_315])).
% 12.19/4.81  tff(c_322, plain, (![A_68]: (k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_68, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_68) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_54, c_319])).
% 12.19/4.81  tff(c_324, plain, (![A_288]: (k3_tmap_1(A_288, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_2(k3_tmap_1(A_288, '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1(A_288, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_288) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(negUnitSimplification, [status(thm)], [c_68, c_322])).
% 12.19/4.81  tff(c_330, plain, (![A_289]: (k3_tmap_1(A_289, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~v1_funct_1(k3_tmap_1(A_289, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_289) | ~l1_pre_topc(A_289) | ~v2_pre_topc(A_289) | v2_struct_0(A_289))), inference(resolution, [status(thm)], [c_257, c_324])).
% 12.19/4.81  tff(c_336, plain, (![A_290]: (k3_tmap_1(A_290, '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~m1_pre_topc('#skF_4', A_290) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(resolution, [status(thm)], [c_226, c_330])).
% 12.19/4.81  tff(c_343, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_336])).
% 12.19/4.81  tff(c_350, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5' | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_343])).
% 12.19/4.81  tff(c_351, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_68, c_350])).
% 12.19/4.81  tff(c_412, plain, (![A_296, B_297, C_295, D_298, E_294]: (k3_tmap_1(A_296, B_297, C_295, D_298, E_294)=k2_partfun1(u1_struct_0(C_295), u1_struct_0(B_297), E_294, u1_struct_0(D_298)) | ~m1_pre_topc(D_298, C_295) | ~m1_subset_1(E_294, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_295), u1_struct_0(B_297)))) | ~v1_funct_2(E_294, u1_struct_0(C_295), u1_struct_0(B_297)) | ~v1_funct_1(E_294) | ~m1_pre_topc(D_298, A_296) | ~m1_pre_topc(C_295, A_296) | ~l1_pre_topc(B_297) | ~v2_pre_topc(B_297) | v2_struct_0(B_297) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.19/4.81  tff(c_418, plain, (![A_296, D_298]: (k3_tmap_1(A_296, '#skF_3', '#skF_4', D_298, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_298)) | ~m1_pre_topc(D_298, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_298, A_296) | ~m1_pre_topc('#skF_4', A_296) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(resolution, [status(thm)], [c_54, c_412])).
% 12.19/4.81  tff(c_423, plain, (![A_296, D_298]: (k3_tmap_1(A_296, '#skF_3', '#skF_4', D_298, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_298)) | ~m1_pre_topc(D_298, '#skF_4') | ~m1_pre_topc(D_298, A_296) | ~m1_pre_topc('#skF_4', A_296) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_418])).
% 12.19/4.81  tff(c_425, plain, (![A_299, D_300]: (k3_tmap_1(A_299, '#skF_3', '#skF_4', D_300, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_300)) | ~m1_pre_topc(D_300, '#skF_4') | ~m1_pre_topc(D_300, A_299) | ~m1_pre_topc('#skF_4', A_299) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299) | v2_struct_0(A_299))), inference(negUnitSimplification, [status(thm)], [c_68, c_423])).
% 12.19/4.81  tff(c_429, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_425])).
% 12.19/4.81  tff(c_433, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_351, c_429])).
% 12.19/4.81  tff(c_434, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_433])).
% 12.19/4.81  tff(c_435, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_434])).
% 12.19/4.81  tff(c_438, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_435])).
% 12.19/4.81  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_438])).
% 12.19/4.81  tff(c_444, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_434])).
% 12.19/4.81  tff(c_443, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))='#skF_5'), inference(splitRight, [status(thm)], [c_434])).
% 12.19/4.81  tff(c_228, plain, (![A_250, B_251, C_252, D_253]: (k2_partfun1(u1_struct_0(A_250), u1_struct_0(B_251), C_252, u1_struct_0(D_253))=k2_tmap_1(A_250, B_251, C_252, D_253) | ~m1_pre_topc(D_253, A_250) | ~m1_subset_1(C_252, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_250), u1_struct_0(B_251)))) | ~v1_funct_2(C_252, u1_struct_0(A_250), u1_struct_0(B_251)) | ~v1_funct_1(C_252) | ~l1_pre_topc(B_251) | ~v2_pre_topc(B_251) | v2_struct_0(B_251) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.19/4.81  tff(c_232, plain, (![D_253]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_253))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_253) | ~m1_pre_topc(D_253, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_228])).
% 12.19/4.81  tff(c_236, plain, (![D_253]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_253))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_253) | ~m1_pre_topc(D_253, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_86, c_66, c_64, c_58, c_56, c_232])).
% 12.19/4.81  tff(c_237, plain, (![D_253]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_253))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_253) | ~m1_pre_topc(D_253, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_236])).
% 12.19/4.81  tff(c_476, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_443, c_237])).
% 12.19/4.81  tff(c_483, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_444, c_476])).
% 12.19/4.81  tff(c_748, plain, (![B_323, D_322, A_320, C_319, E_321]: (r2_hidden('#skF_2'(C_319, A_320, E_321, D_322, B_323), u1_struct_0(C_319)) | r2_funct_2(u1_struct_0(C_319), u1_struct_0(A_320), k2_tmap_1(B_323, A_320, D_322, C_319), E_321) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_319), u1_struct_0(A_320)))) | ~v1_funct_2(E_321, u1_struct_0(C_319), u1_struct_0(A_320)) | ~v1_funct_1(E_321) | ~m1_subset_1(D_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_323), u1_struct_0(A_320)))) | ~v1_funct_2(D_322, u1_struct_0(B_323), u1_struct_0(A_320)) | ~v1_funct_1(D_322) | ~m1_pre_topc(C_319, B_323) | v2_struct_0(C_319) | ~l1_pre_topc(B_323) | ~v2_pre_topc(B_323) | v2_struct_0(B_323) | ~l1_pre_topc(A_320) | ~v2_pre_topc(A_320) | v2_struct_0(A_320))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.19/4.81  tff(c_1508, plain, (![B_415, A_416, D_417, B_418]: (r2_hidden('#skF_2'(B_415, A_416, k4_tmap_1(A_416, B_415), D_417, B_418), u1_struct_0(B_415)) | r2_funct_2(u1_struct_0(B_415), u1_struct_0(A_416), k2_tmap_1(B_418, A_416, D_417, B_415), k4_tmap_1(A_416, B_415)) | ~v1_funct_2(k4_tmap_1(A_416, B_415), u1_struct_0(B_415), u1_struct_0(A_416)) | ~v1_funct_1(k4_tmap_1(A_416, B_415)) | ~m1_subset_1(D_417, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_418), u1_struct_0(A_416)))) | ~v1_funct_2(D_417, u1_struct_0(B_418), u1_struct_0(A_416)) | ~v1_funct_1(D_417) | ~m1_pre_topc(B_415, B_418) | v2_struct_0(B_415) | ~l1_pre_topc(B_418) | ~v2_pre_topc(B_418) | v2_struct_0(B_418) | ~m1_pre_topc(B_415, A_416) | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(resolution, [status(thm)], [c_28, c_748])).
% 12.19/4.81  tff(c_1513, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_483, c_1508])).
% 12.19/4.81  tff(c_1516, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_97, c_86, c_444, c_58, c_56, c_54, c_1513])).
% 12.19/4.81  tff(c_1517, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1516])).
% 12.19/4.81  tff(c_1518, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1517])).
% 12.19/4.81  tff(c_1521, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1518])).
% 12.19/4.81  tff(c_1524, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1521])).
% 12.19/4.81  tff(c_1526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1524])).
% 12.19/4.81  tff(c_1528, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1517])).
% 12.19/4.81  tff(c_1527, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1517])).
% 12.19/4.81  tff(c_1545, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1527])).
% 12.19/4.81  tff(c_1548, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_1545])).
% 12.19/4.81  tff(c_1551, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1548])).
% 12.19/4.81  tff(c_1553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1551])).
% 12.19/4.81  tff(c_1555, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1527])).
% 12.19/4.81  tff(c_1554, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1527])).
% 12.19/4.81  tff(c_1556, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1554])).
% 12.19/4.81  tff(c_1558, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1556, c_12])).
% 12.19/4.81  tff(c_1561, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1528, c_1555, c_1558])).
% 12.19/4.81  tff(c_1575, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1561])).
% 12.19/4.81  tff(c_1578, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1575])).
% 12.19/4.81  tff(c_1581, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1578])).
% 12.19/4.81  tff(c_1583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1581])).
% 12.19/4.81  tff(c_1584, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_1561])).
% 12.19/4.81  tff(c_1589, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_50])).
% 12.19/4.81  tff(c_1595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_1589])).
% 12.19/4.81  tff(c_1596, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1554])).
% 12.19/4.81  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.19/4.81  tff(c_1617, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1596, c_2])).
% 12.19/4.81  tff(c_1626, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_1617])).
% 12.19/4.81  tff(c_1628, plain, (m1_subset_1('#skF_1'(u1_struct_0('#skF_4')), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_112])).
% 12.19/4.81  tff(c_1664, plain, (![A_437, B_438, C_439]: (k1_funct_1(k4_tmap_1(A_437, B_438), C_439)=C_439 | ~r2_hidden(C_439, u1_struct_0(B_438)) | ~m1_subset_1(C_439, u1_struct_0(A_437)) | ~m1_pre_topc(B_438, A_437) | v2_struct_0(B_438) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.19/4.81  tff(c_1670, plain, (![A_440, B_441]: (k1_funct_1(k4_tmap_1(A_440, B_441), '#skF_1'(u1_struct_0(B_441)))='#skF_1'(u1_struct_0(B_441)) | ~m1_subset_1('#skF_1'(u1_struct_0(B_441)), u1_struct_0(A_440)) | ~m1_pre_topc(B_441, A_440) | v2_struct_0(B_441) | ~l1_pre_topc(A_440) | ~v2_pre_topc(A_440) | v2_struct_0(A_440) | v1_xboole_0(u1_struct_0(B_441)))), inference(resolution, [status(thm)], [c_4, c_1664])).
% 12.19/4.81  tff(c_1672, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4')))='#skF_1'(u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1628, c_1670])).
% 12.19/4.81  tff(c_1677, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4')))='#skF_1'(u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1672])).
% 12.19/4.81  tff(c_1678, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_1'(u1_struct_0('#skF_4')))='#skF_1'(u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1677])).
% 12.19/4.81  tff(c_1680, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1678])).
% 12.19/4.81  tff(c_1802, plain, (![E_499, C_500, D_503, A_501, B_502]: (k3_tmap_1(A_501, B_502, C_500, D_503, E_499)=k2_partfun1(u1_struct_0(C_500), u1_struct_0(B_502), E_499, u1_struct_0(D_503)) | ~m1_pre_topc(D_503, C_500) | ~m1_subset_1(E_499, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_500), u1_struct_0(B_502)))) | ~v1_funct_2(E_499, u1_struct_0(C_500), u1_struct_0(B_502)) | ~v1_funct_1(E_499) | ~m1_pre_topc(D_503, A_501) | ~m1_pre_topc(C_500, A_501) | ~l1_pre_topc(B_502) | ~v2_pre_topc(B_502) | v2_struct_0(B_502) | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501))), inference(cnfTransformation, [status(thm)], [f_141])).
% 12.19/4.81  tff(c_1808, plain, (![A_501, D_503]: (k3_tmap_1(A_501, '#skF_3', '#skF_4', D_503, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_503)) | ~m1_pre_topc(D_503, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_503, A_501) | ~m1_pre_topc('#skF_4', A_501) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501))), inference(resolution, [status(thm)], [c_54, c_1802])).
% 12.19/4.81  tff(c_1813, plain, (![A_501, D_503]: (k3_tmap_1(A_501, '#skF_3', '#skF_4', D_503, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_503)) | ~m1_pre_topc(D_503, '#skF_4') | ~m1_pre_topc(D_503, A_501) | ~m1_pre_topc('#skF_4', A_501) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1808])).
% 12.19/4.81  tff(c_1815, plain, (![A_504, D_505]: (k3_tmap_1(A_504, '#skF_3', '#skF_4', D_505, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_505)) | ~m1_pre_topc(D_505, '#skF_4') | ~m1_pre_topc(D_505, A_504) | ~m1_pre_topc('#skF_4', A_504) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(negUnitSimplification, [status(thm)], [c_68, c_1813])).
% 12.19/4.81  tff(c_1819, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1815])).
% 12.19/4.81  tff(c_1823, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1819])).
% 12.19/4.81  tff(c_1824, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_1823])).
% 12.19/4.81  tff(c_1825, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_1824])).
% 12.19/4.81  tff(c_1828, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1825])).
% 12.19/4.81  tff(c_1832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1828])).
% 12.19/4.81  tff(c_1834, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_1824])).
% 12.19/4.81  tff(c_1833, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_1824])).
% 12.19/4.81  tff(c_1725, plain, (![A_465, B_466, C_467, D_468]: (k2_partfun1(u1_struct_0(A_465), u1_struct_0(B_466), C_467, u1_struct_0(D_468))=k2_tmap_1(A_465, B_466, C_467, D_468) | ~m1_pre_topc(D_468, A_465) | ~m1_subset_1(C_467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_465), u1_struct_0(B_466)))) | ~v1_funct_2(C_467, u1_struct_0(A_465), u1_struct_0(B_466)) | ~v1_funct_1(C_467) | ~l1_pre_topc(B_466) | ~v2_pre_topc(B_466) | v2_struct_0(B_466) | ~l1_pre_topc(A_465) | ~v2_pre_topc(A_465) | v2_struct_0(A_465))), inference(cnfTransformation, [status(thm)], [f_109])).
% 12.19/4.81  tff(c_1729, plain, (![D_468]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_468))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_468) | ~m1_pre_topc(D_468, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_54, c_1725])).
% 12.19/4.81  tff(c_1733, plain, (![D_468]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_468))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_468) | ~m1_pre_topc(D_468, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_86, c_66, c_64, c_58, c_56, c_1729])).
% 12.19/4.81  tff(c_1734, plain, (![D_468]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', u1_struct_0(D_468))=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', D_468) | ~m1_pre_topc(D_468, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_68, c_1733])).
% 12.19/4.81  tff(c_1859, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1833, c_1734])).
% 12.19/4.81  tff(c_1866, plain, (k3_tmap_1('#skF_3', '#skF_3', '#skF_4', '#skF_4', '#skF_5')=k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1834, c_1859])).
% 12.19/4.81  tff(c_1874, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1866, c_22])).
% 12.19/4.81  tff(c_1887, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_66, c_64, c_60, c_60, c_58, c_56, c_54, c_1874])).
% 12.19/4.81  tff(c_1888, plain, (m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_1887])).
% 12.19/4.81  tff(c_1714, plain, (![D_458, C_459, B_460, A_462, E_461]: (v1_funct_1(k3_tmap_1(A_462, B_460, C_459, D_458, E_461)) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_459), u1_struct_0(B_460)))) | ~v1_funct_2(E_461, u1_struct_0(C_459), u1_struct_0(B_460)) | ~v1_funct_1(E_461) | ~m1_pre_topc(D_458, A_462) | ~m1_pre_topc(C_459, A_462) | ~l1_pre_topc(B_460) | ~v2_pre_topc(B_460) | v2_struct_0(B_460) | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.19/4.81  tff(c_1718, plain, (![A_462, D_458]: (v1_funct_1(k3_tmap_1(A_462, '#skF_3', '#skF_4', D_458, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_458, A_462) | ~m1_pre_topc('#skF_4', A_462) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(resolution, [status(thm)], [c_54, c_1714])).
% 12.19/4.81  tff(c_1722, plain, (![A_462, D_458]: (v1_funct_1(k3_tmap_1(A_462, '#skF_3', '#skF_4', D_458, '#skF_5')) | ~m1_pre_topc(D_458, A_462) | ~m1_pre_topc('#skF_4', A_462) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1718])).
% 12.19/4.81  tff(c_1723, plain, (![A_462, D_458]: (v1_funct_1(k3_tmap_1(A_462, '#skF_3', '#skF_4', D_458, '#skF_5')) | ~m1_pre_topc(D_458, A_462) | ~m1_pre_topc('#skF_4', A_462) | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(negUnitSimplification, [status(thm)], [c_68, c_1722])).
% 12.19/4.81  tff(c_1883, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1866, c_1723])).
% 12.19/4.81  tff(c_1896, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_60, c_1883])).
% 12.19/4.81  tff(c_1897, plain, (v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1896])).
% 12.19/4.81  tff(c_1765, plain, (![A_487, C_484, B_485, D_483, E_486]: (v1_funct_2(k3_tmap_1(A_487, B_485, C_484, D_483, E_486), u1_struct_0(D_483), u1_struct_0(B_485)) | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_484), u1_struct_0(B_485)))) | ~v1_funct_2(E_486, u1_struct_0(C_484), u1_struct_0(B_485)) | ~v1_funct_1(E_486) | ~m1_pre_topc(D_483, A_487) | ~m1_pre_topc(C_484, A_487) | ~l1_pre_topc(B_485) | ~v2_pre_topc(B_485) | v2_struct_0(B_485) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(cnfTransformation, [status(thm)], [f_171])).
% 12.19/4.81  tff(c_1769, plain, (![A_487, D_483]: (v1_funct_2(k3_tmap_1(A_487, '#skF_3', '#skF_4', D_483, '#skF_5'), u1_struct_0(D_483), u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_483, A_487) | ~m1_pre_topc('#skF_4', A_487) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(resolution, [status(thm)], [c_54, c_1765])).
% 12.19/4.81  tff(c_1773, plain, (![A_487, D_483]: (v1_funct_2(k3_tmap_1(A_487, '#skF_3', '#skF_4', D_483, '#skF_5'), u1_struct_0(D_483), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_483, A_487) | ~m1_pre_topc('#skF_4', A_487) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1769])).
% 12.19/4.81  tff(c_1774, plain, (![A_487, D_483]: (v1_funct_2(k3_tmap_1(A_487, '#skF_3', '#skF_4', D_483, '#skF_5'), u1_struct_0(D_483), u1_struct_0('#skF_3')) | ~m1_pre_topc(D_483, A_487) | ~m1_pre_topc('#skF_4', A_487) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(negUnitSimplification, [status(thm)], [c_68, c_1773])).
% 12.19/4.81  tff(c_1877, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1866, c_1774])).
% 12.19/4.81  tff(c_1890, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_60, c_1877])).
% 12.19/4.81  tff(c_1891, plain, (v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1890])).
% 12.19/4.81  tff(c_1749, plain, (![C_478, B_479, D_480, A_481]: (r2_funct_2(u1_struct_0(C_478), u1_struct_0(B_479), D_480, k3_tmap_1(A_481, B_479, C_478, C_478, D_480)) | ~m1_subset_1(D_480, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_478), u1_struct_0(B_479)))) | ~v1_funct_2(D_480, u1_struct_0(C_478), u1_struct_0(B_479)) | ~v1_funct_1(D_480) | ~m1_pre_topc(C_478, A_481) | v2_struct_0(C_478) | ~l1_pre_topc(B_479) | ~v2_pre_topc(B_479) | v2_struct_0(B_479) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(cnfTransformation, [status(thm)], [f_271])).
% 12.19/4.81  tff(c_1753, plain, (![A_481]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_481, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_481) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(resolution, [status(thm)], [c_54, c_1749])).
% 12.19/4.81  tff(c_1757, plain, (![A_481]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_481, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_481) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_58, c_56, c_1753])).
% 12.19/4.81  tff(c_1758, plain, (![A_481]: (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k3_tmap_1(A_481, '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', A_481) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_1757])).
% 12.19/4.81  tff(c_1880, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1866, c_1758])).
% 12.19/4.81  tff(c_1893, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1880])).
% 12.19/4.81  tff(c_1894, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1893])).
% 12.19/4.81  tff(c_1914, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_1894, c_12])).
% 12.19/4.81  tff(c_1917, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5' | ~m1_subset_1(k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1897, c_1891, c_1914])).
% 12.19/4.81  tff(c_2028, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1888, c_1917])).
% 12.19/4.81  tff(c_1900, plain, (![A_507, B_510, E_508, C_506, D_509]: (r2_hidden('#skF_2'(C_506, A_507, E_508, D_509, B_510), u1_struct_0(C_506)) | r2_funct_2(u1_struct_0(C_506), u1_struct_0(A_507), k2_tmap_1(B_510, A_507, D_509, C_506), E_508) | ~m1_subset_1(E_508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_506), u1_struct_0(A_507)))) | ~v1_funct_2(E_508, u1_struct_0(C_506), u1_struct_0(A_507)) | ~v1_funct_1(E_508) | ~m1_subset_1(D_509, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_510), u1_struct_0(A_507)))) | ~v1_funct_2(D_509, u1_struct_0(B_510), u1_struct_0(A_507)) | ~v1_funct_1(D_509) | ~m1_pre_topc(C_506, B_510) | v2_struct_0(C_506) | ~l1_pre_topc(B_510) | ~v2_pre_topc(B_510) | v2_struct_0(B_510) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.19/4.81  tff(c_3199, plain, (![B_628, A_629, D_630, B_631]: (r2_hidden('#skF_2'(B_628, A_629, k4_tmap_1(A_629, B_628), D_630, B_631), u1_struct_0(B_628)) | r2_funct_2(u1_struct_0(B_628), u1_struct_0(A_629), k2_tmap_1(B_631, A_629, D_630, B_628), k4_tmap_1(A_629, B_628)) | ~v1_funct_2(k4_tmap_1(A_629, B_628), u1_struct_0(B_628), u1_struct_0(A_629)) | ~v1_funct_1(k4_tmap_1(A_629, B_628)) | ~m1_subset_1(D_630, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_631), u1_struct_0(A_629)))) | ~v1_funct_2(D_630, u1_struct_0(B_631), u1_struct_0(A_629)) | ~v1_funct_1(D_630) | ~m1_pre_topc(B_628, B_631) | v2_struct_0(B_628) | ~l1_pre_topc(B_631) | ~v2_pre_topc(B_631) | v2_struct_0(B_631) | ~m1_pre_topc(B_628, A_629) | ~l1_pre_topc(A_629) | ~v2_pre_topc(A_629) | v2_struct_0(A_629))), inference(resolution, [status(thm)], [c_28, c_1900])).
% 12.19/4.81  tff(c_3204, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2028, c_3199])).
% 12.19/4.81  tff(c_3207, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_97, c_86, c_1834, c_58, c_56, c_54, c_3204])).
% 12.19/4.81  tff(c_3208, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_3207])).
% 12.19/4.81  tff(c_3209, plain, (~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3208])).
% 12.19/4.81  tff(c_3212, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_3209])).
% 12.19/4.81  tff(c_3215, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_3212])).
% 12.19/4.81  tff(c_3217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3215])).
% 12.19/4.81  tff(c_3219, plain, (v1_funct_1(k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_3208])).
% 12.19/4.81  tff(c_3218, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3208])).
% 12.19/4.81  tff(c_3238, plain, (~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3218])).
% 12.19/4.81  tff(c_3241, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_3238])).
% 12.19/4.81  tff(c_3244, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_3241])).
% 12.19/4.81  tff(c_3246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3244])).
% 12.19/4.81  tff(c_3248, plain, (v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_3218])).
% 12.19/4.81  tff(c_3247, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4')) | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_3218])).
% 12.19/4.81  tff(c_3249, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3247])).
% 12.19/4.81  tff(c_3251, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_3249, c_12])).
% 12.19/4.81  tff(c_3254, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5' | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_3219, c_3248, c_3251])).
% 12.19/4.81  tff(c_3268, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_3254])).
% 12.19/4.81  tff(c_3271, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_3268])).
% 12.19/4.81  tff(c_3274, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_3271])).
% 12.19/4.81  tff(c_3276, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_3274])).
% 12.19/4.81  tff(c_3277, plain, (k4_tmap_1('#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_3254])).
% 12.19/4.81  tff(c_3282, plain, (~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3277, c_50])).
% 12.19/4.81  tff(c_3288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_3282])).
% 12.19/4.81  tff(c_3289, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3247])).
% 12.19/4.81  tff(c_3316, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_3289, c_2])).
% 12.19/4.81  tff(c_3325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1680, c_3316])).
% 12.19/4.81  tff(c_3327, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1678])).
% 12.19/4.81  tff(c_4769, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_4728])).
% 12.19/4.81  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k3_funct_2(A_8, B_9, C_10, D_11)=k1_funct_1(C_10, D_11) | ~m1_subset_1(D_11, A_8) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))) | ~v1_funct_2(C_10, A_8, B_9) | ~v1_funct_1(C_10) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.19/4.81  tff(c_4782, plain, (![B_9, C_10]: (k3_funct_2(u1_struct_0('#skF_4'), B_9, C_10, '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))=k1_funct_1(C_10, '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4')) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_9))) | ~v1_funct_2(C_10, u1_struct_0('#skF_4'), B_9) | ~v1_funct_1(C_10) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4769, c_8])).
% 12.19/4.81  tff(c_4786, plain, (![B_842, C_843]: (k3_funct_2(u1_struct_0('#skF_4'), B_842, C_843, '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))=k1_funct_1(C_843, '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4')) | ~m1_subset_1(C_843, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), B_842))) | ~v1_funct_2(C_843, u1_struct_0('#skF_4'), B_842) | ~v1_funct_1(C_843))), inference(negUnitSimplification, [status(thm)], [c_3327, c_4782])).
% 12.19/4.81  tff(c_4790, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))=k1_funct_1(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4')) | ~v1_funct_2(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k3_tmap_1('#skF_4', '#skF_3', '#skF_4', '#skF_4', '#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_3781, c_4786])).
% 12.19/4.81  tff(c_4812, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))=k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_97, c_3630, c_58, c_3518, c_56, c_3518, c_3518, c_3518, c_4790])).
% 12.19/4.81  tff(c_4813, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))=k1_funct_1('#skF_5', '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_4812])).
% 12.19/4.81  tff(c_4882, plain, (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4876, c_4813])).
% 12.19/4.81  tff(c_38, plain, (![B_111, C_127, D_135, E_139, A_79]: (k3_funct_2(u1_struct_0(B_111), u1_struct_0(A_79), D_135, '#skF_2'(C_127, A_79, E_139, D_135, B_111))!=k1_funct_1(E_139, '#skF_2'(C_127, A_79, E_139, D_135, B_111)) | r2_funct_2(u1_struct_0(C_127), u1_struct_0(A_79), k2_tmap_1(B_111, A_79, D_135, C_127), E_139) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_127), u1_struct_0(A_79)))) | ~v1_funct_2(E_139, u1_struct_0(C_127), u1_struct_0(A_79)) | ~v1_funct_1(E_139) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_111), u1_struct_0(A_79)))) | ~v1_funct_2(D_135, u1_struct_0(B_111), u1_struct_0(A_79)) | ~v1_funct_1(D_135) | ~m1_pre_topc(C_127, B_111) | v2_struct_0(C_127) | ~l1_pre_topc(B_111) | ~v2_pre_topc(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_79) | ~v2_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.19/4.81  tff(c_4889, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))!='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_4', '#skF_3', '#skF_5', '#skF_4'), k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2(k4_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1(k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4882, c_38])).
% 12.19/4.81  tff(c_4893, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))!='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_5', k4_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_97, c_86, c_3630, c_58, c_56, c_54, c_4702, c_4729, c_3669, c_4889])).
% 12.19/4.81  tff(c_4894, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))!='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | ~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_4770, c_4893])).
% 12.19/4.81  tff(c_4936, plain, (~m1_subset_1(k4_tmap_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_4894])).
% 12.19/4.81  tff(c_4939, plain, (~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_28, c_4936])).
% 12.19/4.81  tff(c_4942, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_4939])).
% 12.19/4.81  tff(c_4944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_4942])).
% 12.19/4.81  tff(c_4945, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))!='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_4894])).
% 12.19/4.81  tff(c_4877, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_4861])).
% 12.19/4.81  tff(c_48, plain, (![A_163, B_167, C_169]: (k1_funct_1(k4_tmap_1(A_163, B_167), C_169)=C_169 | ~r2_hidden(C_169, u1_struct_0(B_167)) | ~m1_subset_1(C_169, u1_struct_0(A_163)) | ~m1_pre_topc(B_167, A_163) | v2_struct_0(B_167) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_303])).
% 12.19/4.81  tff(c_4848, plain, (![A_163]: (k1_funct_1(k4_tmap_1(A_163, '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0(A_163)) | ~m1_pre_topc('#skF_4', A_163) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(resolution, [status(thm)], [c_4846, c_48])).
% 12.19/4.81  tff(c_13047, plain, (![A_1200]: (k1_funct_1(k4_tmap_1(A_1200, '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'), u1_struct_0(A_1200)) | ~m1_pre_topc('#skF_4', A_1200) | ~l1_pre_topc(A_1200) | ~v2_pre_topc(A_1200) | v2_struct_0(A_1200))), inference(negUnitSimplification, [status(thm)], [c_62, c_4848])).
% 12.19/4.81  tff(c_13050, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_4877, c_13047])).
% 12.19/4.81  tff(c_13061, plain, (k1_funct_1(k4_tmap_1('#skF_3', '#skF_4'), '#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4'))='#skF_2'('#skF_4', '#skF_3', k4_tmap_1('#skF_3', '#skF_4'), '#skF_5', '#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_13050])).
% 12.19/4.81  tff(c_13063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_4945, c_13061])).
% 12.19/4.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.19/4.81  
% 12.19/4.81  Inference rules
% 12.19/4.81  ----------------------
% 12.19/4.81  #Ref     : 0
% 12.19/4.81  #Sup     : 2487
% 12.19/4.81  #Fact    : 0
% 12.19/4.81  #Define  : 0
% 12.19/4.82  #Split   : 45
% 12.19/4.82  #Chain   : 0
% 12.19/4.82  #Close   : 0
% 12.19/4.82  
% 12.19/4.82  Ordering : KBO
% 12.19/4.82  
% 12.19/4.82  Simplification rules
% 12.19/4.82  ----------------------
% 12.19/4.82  #Subsume      : 538
% 12.19/4.82  #Demod        : 7857
% 12.19/4.82  #Tautology    : 813
% 12.19/4.82  #SimpNegUnit  : 1230
% 12.19/4.82  #BackRed      : 134
% 12.19/4.82  
% 12.19/4.82  #Partial instantiations: 0
% 12.19/4.82  #Strategies tried      : 1
% 12.19/4.82  
% 12.19/4.82  Timing (in seconds)
% 12.19/4.82  ----------------------
% 12.19/4.82  Preprocessing        : 0.42
% 12.19/4.82  Parsing              : 0.22
% 12.19/4.82  CNF conversion       : 0.04
% 12.19/4.82  Main loop            : 3.59
% 12.19/4.82  Inferencing          : 1.13
% 12.19/4.82  Reduction            : 1.29
% 12.19/4.82  Demodulation         : 1.01
% 12.19/4.82  BG Simplification    : 0.11
% 12.19/4.82  Subsumption          : 0.90
% 12.19/4.82  Abstraction          : 0.17
% 12.19/4.82  MUC search           : 0.00
% 12.19/4.82  Cooper               : 0.00
% 12.19/4.82  Total                : 4.12
% 12.19/4.82  Index Insertion      : 0.00
% 12.19/4.82  Index Deletion       : 0.00
% 12.19/4.82  Index Matching       : 0.00
% 12.19/4.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
