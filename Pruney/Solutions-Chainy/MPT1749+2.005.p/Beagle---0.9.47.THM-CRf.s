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
% DateTime   : Thu Dec  3 10:26:50 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 798 expanded)
%              Number of leaves         :   36 ( 298 expanded)
%              Depth                    :   21
%              Number of atoms          :  394 (6864 expanded)
%              Number of equality atoms :   47 ( 547 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

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

tff(f_179,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,A,B)
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,D,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                     => ( ! [F] :
                            ( m1_subset_1(F,A)
                           => ( r2_hidden(F,D)
                             => k3_funct_2(A,B,C,F) = k1_funct_1(E,F) ) )
                       => k2_partfun1(A,B,C,D) = E ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_127,axiom,(
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

tff(c_32,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_30,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_4,plain,(
    ! [D_9,A_1,B_2,C_3] :
      ( k1_funct_1(D_9,'#skF_1'(A_1,B_2,C_3,D_9)) != k1_funct_1(C_3,'#skF_1'(A_1,B_2,C_3,D_9))
      | r2_funct_2(A_1,B_2,C_3,D_9)
      | ~ m1_subset_1(D_9,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_9,A_1,B_2)
      | ~ v1_funct_1(D_9)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_funct_2(A_178,B_179,C_180,C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_2(C_180,A_178,B_179)
      | ~ v1_funct_1(C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_2(C_180,A_178,B_179)
      | ~ v1_funct_1(C_180) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4])).

tff(c_109,plain,
    ( r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_114,plain,(
    r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_109])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_44,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_14,plain,(
    ! [A_75] :
      ( l1_struct_0(A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_50,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_142,plain,(
    ! [A_190,B_191,D_193,C_189,E_192] :
      ( m1_subset_1('#skF_2'(C_189,A_190,B_191,E_192,D_193),A_190)
      | k2_partfun1(A_190,B_191,C_189,D_193) = E_192
      | ~ m1_subset_1(E_192,k1_zfmisc_1(k2_zfmisc_1(D_193,B_191)))
      | ~ v1_funct_2(E_192,D_193,B_191)
      | ~ v1_funct_1(E_192)
      | ~ m1_subset_1(D_193,k1_zfmisc_1(A_190))
      | v1_xboole_0(D_193)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_2(C_189,A_190,B_191)
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(B_191)
      | v1_xboole_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_144,plain,(
    ! [C_189,A_190] :
      ( m1_subset_1('#skF_2'(C_189,A_190,u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),A_190)
      | k2_partfun1(A_190,u1_struct_0('#skF_3'),C_189,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_190))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_189,A_190,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_28,c_142])).

tff(c_149,plain,(
    ! [C_189,A_190] :
      ( m1_subset_1('#skF_2'(C_189,A_190,u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),A_190)
      | k2_partfun1(A_190,u1_struct_0('#skF_3'),C_189,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_190))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_189,A_190,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_144])).

tff(c_164,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_18,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(u1_struct_0(A_79))
      | ~ l1_struct_0(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_167,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_164,c_18])).

tff(c_170,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_167])).

tff(c_173,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_170])).

tff(c_177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_173])).

tff(c_179,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_36,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_146,plain,(
    ! [C_189,A_190] :
      ( m1_subset_1('#skF_2'(C_189,A_190,u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')),A_190)
      | k2_partfun1(A_190,u1_struct_0('#skF_3'),C_189,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_190))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_189,A_190,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_152,plain,(
    ! [C_189,A_190] :
      ( m1_subset_1('#skF_2'(C_189,A_190,u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')),A_190)
      | k2_partfun1(A_190,u1_struct_0('#skF_3'),C_189,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_190))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_189,A_190,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_146])).

tff(c_228,plain,(
    ! [C_189,A_190] :
      ( m1_subset_1('#skF_2'(C_189,A_190,u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_4')),A_190)
      | k2_partfun1(A_190,u1_struct_0('#skF_3'),C_189,u1_struct_0('#skF_4')) = '#skF_6'
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(A_190))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_189,A_190,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(A_190) ) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_152])).

tff(c_229,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_232,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_229,c_18])).

tff(c_235,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_232])).

tff(c_238,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_235])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_238])).

tff(c_244,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_22,plain,(
    ! [B_97,A_95] :
      ( m1_subset_1(u1_struct_0(B_97),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_pre_topc(B_97,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_57,plain,(
    ! [B_158,A_159] :
      ( l1_pre_topc(B_158)
      | ~ m1_pre_topc(B_158,A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_63,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_60])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_178,plain,(
    ! [C_189,A_190] :
      ( v1_xboole_0(u1_struct_0('#skF_5'))
      | m1_subset_1('#skF_2'(C_189,A_190,u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),A_190)
      | k2_partfun1(A_190,u1_struct_0('#skF_3'),C_189,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_190))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_189,A_190,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(A_190) ) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_181,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_184,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_181,c_18])).

tff(c_187,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_184])).

tff(c_190,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_190])).

tff(c_196,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_153,plain,(
    ! [A_195,E_197,C_194,B_196,D_198] :
      ( r2_hidden('#skF_2'(C_194,A_195,B_196,E_197,D_198),D_198)
      | k2_partfun1(A_195,B_196,C_194,D_198) = E_197
      | ~ m1_subset_1(E_197,k1_zfmisc_1(k2_zfmisc_1(D_198,B_196)))
      | ~ v1_funct_2(E_197,D_198,B_196)
      | ~ v1_funct_1(E_197)
      | ~ m1_subset_1(D_198,k1_zfmisc_1(A_195))
      | v1_xboole_0(D_198)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_195,B_196)))
      | ~ v1_funct_2(C_194,A_195,B_196)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(B_196)
      | v1_xboole_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_155,plain,(
    ! [C_194,A_195] :
      ( r2_hidden('#skF_2'(C_194,A_195,u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_195,u1_struct_0('#skF_3'),C_194,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_195))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_195,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_194,A_195,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_195) ) ),
    inference(resolution,[status(thm)],[c_28,c_153])).

tff(c_160,plain,(
    ! [C_194,A_195] :
      ( r2_hidden('#skF_2'(C_194,A_195,u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_195,u1_struct_0('#skF_3'),C_194,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_195))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_195,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_194,A_195,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_155])).

tff(c_271,plain,(
    ! [C_194,A_195] :
      ( r2_hidden('#skF_2'(C_194,A_195,u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | k2_partfun1(A_195,u1_struct_0('#skF_3'),C_194,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_195))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_195,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_194,A_195,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(A_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_196,c_160])).

tff(c_26,plain,(
    ! [F_155] :
      ( k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',F_155) = k1_funct_1('#skF_7',F_155)
      | ~ r2_hidden(F_155,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_155,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_197,plain,(
    ! [E_205,B_204,A_203,C_202,D_206] :
      ( k3_funct_2(A_203,B_204,C_202,'#skF_2'(C_202,A_203,B_204,E_205,D_206)) != k1_funct_1(E_205,'#skF_2'(C_202,A_203,B_204,E_205,D_206))
      | k2_partfun1(A_203,B_204,C_202,D_206) = E_205
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(D_206,B_204)))
      | ~ v1_funct_2(E_205,D_206,B_204)
      | ~ v1_funct_1(E_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(A_203))
      | v1_xboole_0(D_206)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204)))
      | ~ v1_funct_2(C_202,A_203,B_204)
      | ~ v1_funct_1(C_202)
      | v1_xboole_0(B_204)
      | v1_xboole_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_200,plain,(
    ! [E_205,D_206] :
      ( k1_funct_1(E_205,'#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206)) != k1_funct_1('#skF_7','#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206))
      | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_206) = E_205
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(D_206,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_205,D_206,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_206)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_202,plain,(
    ! [E_205,D_206] :
      ( k1_funct_1(E_205,'#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206)) != k1_funct_1('#skF_7','#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206))
      | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_206) = E_205
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(D_206,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_205,D_206,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_206)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_200])).

tff(c_203,plain,(
    ! [E_205,D_206] :
      ( k1_funct_1(E_205,'#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206)) != k1_funct_1('#skF_7','#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206))
      | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_206) = E_205
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(D_206,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_205,D_206,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_206)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_202])).

tff(c_274,plain,(
    ! [E_205,D_206] :
      ( k1_funct_1(E_205,'#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206)) != k1_funct_1('#skF_7','#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206))
      | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_206) = E_205
      | ~ m1_subset_1(E_205,k1_zfmisc_1(k2_zfmisc_1(D_206,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(E_205,D_206,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(E_205)
      | ~ m1_subset_1(D_206,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_206)
      | ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),E_205,D_206),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_203])).

tff(c_277,plain,(
    ! [D_206] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_206) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_206,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_206,u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_206,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_206)
      | ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',D_206),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',D_206),u1_struct_0('#skF_4')) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_274])).

tff(c_281,plain,(
    ! [D_222] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',D_222) = '#skF_7'
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(D_222,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_7',D_222,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_222,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(D_222)
      | ~ r2_hidden('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',D_222),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',D_222),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_277])).

tff(c_285,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_271,c_281])).

tff(c_288,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_30,c_28,c_285])).

tff(c_289,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_196,c_288])).

tff(c_290,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_293,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_290])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_293])).

tff(c_299,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_195,plain,(
    ! [C_189,A_190] :
      ( m1_subset_1('#skF_2'(C_189,A_190,u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),A_190)
      | k2_partfun1(A_190,u1_struct_0('#skF_3'),C_189,u1_struct_0('#skF_5')) = '#skF_7'
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_190))
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_190,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_189,A_190,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_189)
      | v1_xboole_0(A_190) ) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_298,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_4'))
    | k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_310,plain,(
    ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_313,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_195,c_310])).

tff(c_316,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7'
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_299,c_313])).

tff(c_317,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_316])).

tff(c_46,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_52,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_119,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k2_partfun1(u1_struct_0(A_184),u1_struct_0(B_185),C_186,u1_struct_0(D_187)) = k2_tmap_1(A_184,B_185,C_186,D_187)
      | ~ m1_pre_topc(D_187,A_184)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184),u1_struct_0(B_185))))
      | ~ v1_funct_2(C_186,u1_struct_0(A_184),u1_struct_0(B_185))
      | ~ v1_funct_1(C_186)
      | ~ l1_pre_topc(B_185)
      | ~ v2_pre_topc(B_185)
      | v2_struct_0(B_185)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_123,plain,(
    ! [D_187] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_187)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_187)
      | ~ m1_pre_topc(D_187,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_130,plain,(
    ! [D_187] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_187)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_187)
      | ~ m1_pre_topc(D_187,'#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_52,c_50,c_38,c_36,c_123])).

tff(c_131,plain,(
    ! [D_187] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0(D_187)) = k2_tmap_1('#skF_4','#skF_3','#skF_6',D_187)
      | ~ m1_pre_topc(D_187,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_54,c_130])).

tff(c_321,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7'
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_131])).

tff(c_328,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_321])).

tff(c_24,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_332,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_24])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_332])).

tff(c_336,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'),'#skF_6',u1_struct_0('#skF_5')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_348,plain,
    ( k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7'
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_131])).

tff(c_355,plain,(
    k2_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_348])).

tff(c_359,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_24])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:43:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.42  
% 2.76/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.43  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_funct_2 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.76/1.43  
% 2.76/1.43  %Foreground sorts:
% 2.76/1.43  
% 2.76/1.43  
% 2.76/1.43  %Background operators:
% 2.76/1.43  
% 2.76/1.43  
% 2.76/1.43  %Foreground operators:
% 2.76/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.76/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.76/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.76/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.76/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.76/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.76/1.43  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.76/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.76/1.43  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.76/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.76/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.76/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.43  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.76/1.43  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.76/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.43  
% 3.10/1.45  tff(f_179, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => ((![F]: (m1_subset_1(F, u1_struct_0(B)) => (r2_hidden(F, u1_struct_0(C)) => (k3_funct_2(u1_struct_0(B), u1_struct_0(A), D, F) = k1_funct_1(E, F))))) => r2_funct_2(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 3.10/1.45  tff(f_45, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 3.10/1.45  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.10/1.45  tff(f_81, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, D, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((![F]: (m1_subset_1(F, A) => (r2_hidden(F, D) => (k3_funct_2(A, B, C, F) = k1_funct_1(E, F))))) => (k2_partfun1(A, B, C, D) = E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_2)).
% 3.10/1.45  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.10/1.45  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.10/1.45  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.10/1.45  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.10/1.45  tff(c_32, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_30, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_28, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_4, plain, (![D_9, A_1, B_2, C_3]: (k1_funct_1(D_9, '#skF_1'(A_1, B_2, C_3, D_9))!=k1_funct_1(C_3, '#skF_1'(A_1, B_2, C_3, D_9)) | r2_funct_2(A_1, B_2, C_3, D_9) | ~m1_subset_1(D_9, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_9, A_1, B_2) | ~v1_funct_1(D_9) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.10/1.45  tff(c_107, plain, (![A_178, B_179, C_180]: (r2_funct_2(A_178, B_179, C_180, C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_2(C_180, A_178, B_179) | ~v1_funct_1(C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_2(C_180, A_178, B_179) | ~v1_funct_1(C_180))), inference(reflexivity, [status(thm), theory('equality')], [c_4])).
% 3.10/1.45  tff(c_109, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_107])).
% 3.10/1.45  tff(c_114, plain, (r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_109])).
% 3.10/1.45  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_44, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_14, plain, (![A_75]: (l1_struct_0(A_75) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.10/1.45  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_50, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_54, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_142, plain, (![A_190, B_191, D_193, C_189, E_192]: (m1_subset_1('#skF_2'(C_189, A_190, B_191, E_192, D_193), A_190) | k2_partfun1(A_190, B_191, C_189, D_193)=E_192 | ~m1_subset_1(E_192, k1_zfmisc_1(k2_zfmisc_1(D_193, B_191))) | ~v1_funct_2(E_192, D_193, B_191) | ~v1_funct_1(E_192) | ~m1_subset_1(D_193, k1_zfmisc_1(A_190)) | v1_xboole_0(D_193) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_2(C_189, A_190, B_191) | ~v1_funct_1(C_189) | v1_xboole_0(B_191) | v1_xboole_0(A_190))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.45  tff(c_144, plain, (![C_189, A_190]: (m1_subset_1('#skF_2'(C_189, A_190, u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), A_190) | k2_partfun1(A_190, u1_struct_0('#skF_3'), C_189, u1_struct_0('#skF_5'))='#skF_7' | ~v1_funct_2('#skF_7', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_190)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_189, A_190, u1_struct_0('#skF_3')) | ~v1_funct_1(C_189) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_190))), inference(resolution, [status(thm)], [c_28, c_142])).
% 3.10/1.45  tff(c_149, plain, (![C_189, A_190]: (m1_subset_1('#skF_2'(C_189, A_190, u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), A_190) | k2_partfun1(A_190, u1_struct_0('#skF_3'), C_189, u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_190)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_189, A_190, u1_struct_0('#skF_3')) | ~v1_funct_1(C_189) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_144])).
% 3.10/1.45  tff(c_164, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_149])).
% 3.10/1.45  tff(c_18, plain, (![A_79]: (~v1_xboole_0(u1_struct_0(A_79)) | ~l1_struct_0(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.10/1.45  tff(c_167, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_164, c_18])).
% 3.10/1.45  tff(c_170, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_167])).
% 3.10/1.45  tff(c_173, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_170])).
% 3.10/1.45  tff(c_177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_173])).
% 3.10/1.45  tff(c_179, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_149])).
% 3.10/1.45  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_36, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_146, plain, (![C_189, A_190]: (m1_subset_1('#skF_2'(C_189, A_190, u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4')), A_190) | k2_partfun1(A_190, u1_struct_0('#skF_3'), C_189, u1_struct_0('#skF_4'))='#skF_6' | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_190)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_189, A_190, u1_struct_0('#skF_3')) | ~v1_funct_1(C_189) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_190))), inference(resolution, [status(thm)], [c_34, c_142])).
% 3.10/1.45  tff(c_152, plain, (![C_189, A_190]: (m1_subset_1('#skF_2'(C_189, A_190, u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4')), A_190) | k2_partfun1(A_190, u1_struct_0('#skF_3'), C_189, u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_190)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_189, A_190, u1_struct_0('#skF_3')) | ~v1_funct_1(C_189) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_190))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_146])).
% 3.10/1.45  tff(c_228, plain, (![C_189, A_190]: (m1_subset_1('#skF_2'(C_189, A_190, u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_4')), A_190) | k2_partfun1(A_190, u1_struct_0('#skF_3'), C_189, u1_struct_0('#skF_4'))='#skF_6' | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(A_190)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_189, A_190, u1_struct_0('#skF_3')) | ~v1_funct_1(C_189) | v1_xboole_0(A_190))), inference(negUnitSimplification, [status(thm)], [c_179, c_152])).
% 3.10/1.45  tff(c_229, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_228])).
% 3.10/1.45  tff(c_232, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_229, c_18])).
% 3.10/1.45  tff(c_235, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_48, c_232])).
% 3.10/1.45  tff(c_238, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_235])).
% 3.10/1.45  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_238])).
% 3.10/1.45  tff(c_244, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_228])).
% 3.10/1.45  tff(c_22, plain, (![B_97, A_95]: (m1_subset_1(u1_struct_0(B_97), k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_pre_topc(B_97, A_95) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.10/1.45  tff(c_57, plain, (![B_158, A_159]: (l1_pre_topc(B_158) | ~m1_pre_topc(B_158, A_159) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.10/1.45  tff(c_60, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_57])).
% 3.10/1.45  tff(c_63, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_60])).
% 3.10/1.45  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_178, plain, (![C_189, A_190]: (v1_xboole_0(u1_struct_0('#skF_5')) | m1_subset_1('#skF_2'(C_189, A_190, u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), A_190) | k2_partfun1(A_190, u1_struct_0('#skF_3'), C_189, u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_190)) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_189, A_190, u1_struct_0('#skF_3')) | ~v1_funct_1(C_189) | v1_xboole_0(A_190))), inference(splitRight, [status(thm)], [c_149])).
% 3.10/1.45  tff(c_181, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_178])).
% 3.10/1.45  tff(c_184, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_181, c_18])).
% 3.10/1.45  tff(c_187, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_184])).
% 3.10/1.45  tff(c_190, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_14, c_187])).
% 3.10/1.45  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_190])).
% 3.10/1.45  tff(c_196, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_178])).
% 3.10/1.45  tff(c_153, plain, (![A_195, E_197, C_194, B_196, D_198]: (r2_hidden('#skF_2'(C_194, A_195, B_196, E_197, D_198), D_198) | k2_partfun1(A_195, B_196, C_194, D_198)=E_197 | ~m1_subset_1(E_197, k1_zfmisc_1(k2_zfmisc_1(D_198, B_196))) | ~v1_funct_2(E_197, D_198, B_196) | ~v1_funct_1(E_197) | ~m1_subset_1(D_198, k1_zfmisc_1(A_195)) | v1_xboole_0(D_198) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_195, B_196))) | ~v1_funct_2(C_194, A_195, B_196) | ~v1_funct_1(C_194) | v1_xboole_0(B_196) | v1_xboole_0(A_195))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.45  tff(c_155, plain, (![C_194, A_195]: (r2_hidden('#skF_2'(C_194, A_195, u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | k2_partfun1(A_195, u1_struct_0('#skF_3'), C_194, u1_struct_0('#skF_5'))='#skF_7' | ~v1_funct_2('#skF_7', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_195)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_195, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_194, A_195, u1_struct_0('#skF_3')) | ~v1_funct_1(C_194) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_195))), inference(resolution, [status(thm)], [c_28, c_153])).
% 3.10/1.45  tff(c_160, plain, (![C_194, A_195]: (r2_hidden('#skF_2'(C_194, A_195, u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | k2_partfun1(A_195, u1_struct_0('#skF_3'), C_194, u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_195)) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_195, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_194, A_195, u1_struct_0('#skF_3')) | ~v1_funct_1(C_194) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_155])).
% 3.10/1.45  tff(c_271, plain, (![C_194, A_195]: (r2_hidden('#skF_2'(C_194, A_195, u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | k2_partfun1(A_195, u1_struct_0('#skF_3'), C_194, u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_195)) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_195, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_194, A_195, u1_struct_0('#skF_3')) | ~v1_funct_1(C_194) | v1_xboole_0(A_195))), inference(negUnitSimplification, [status(thm)], [c_179, c_196, c_160])).
% 3.10/1.45  tff(c_26, plain, (![F_155]: (k3_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', F_155)=k1_funct_1('#skF_7', F_155) | ~r2_hidden(F_155, u1_struct_0('#skF_5')) | ~m1_subset_1(F_155, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_197, plain, (![E_205, B_204, A_203, C_202, D_206]: (k3_funct_2(A_203, B_204, C_202, '#skF_2'(C_202, A_203, B_204, E_205, D_206))!=k1_funct_1(E_205, '#skF_2'(C_202, A_203, B_204, E_205, D_206)) | k2_partfun1(A_203, B_204, C_202, D_206)=E_205 | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(D_206, B_204))) | ~v1_funct_2(E_205, D_206, B_204) | ~v1_funct_1(E_205) | ~m1_subset_1(D_206, k1_zfmisc_1(A_203)) | v1_xboole_0(D_206) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))) | ~v1_funct_2(C_202, A_203, B_204) | ~v1_funct_1(C_202) | v1_xboole_0(B_204) | v1_xboole_0(A_203))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.10/1.45  tff(c_200, plain, (![E_205, D_206]: (k1_funct_1(E_205, '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206))!=k1_funct_1('#skF_7', '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206)) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_206)=E_205 | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(D_206, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_205, D_206, u1_struct_0('#skF_3')) | ~v1_funct_1(E_205) | ~m1_subset_1(D_206, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(D_206) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_26, c_197])).
% 3.10/1.45  tff(c_202, plain, (![E_205, D_206]: (k1_funct_1(E_205, '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206))!=k1_funct_1('#skF_7', '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206)) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_206)=E_205 | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(D_206, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_205, D_206, u1_struct_0('#skF_3')) | ~v1_funct_1(E_205) | ~m1_subset_1(D_206, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(D_206) | v1_xboole_0(u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_200])).
% 3.10/1.45  tff(c_203, plain, (![E_205, D_206]: (k1_funct_1(E_205, '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206))!=k1_funct_1('#skF_7', '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206)) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_206)=E_205 | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(D_206, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_205, D_206, u1_struct_0('#skF_3')) | ~v1_funct_1(E_205) | ~m1_subset_1(D_206, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(D_206) | v1_xboole_0(u1_struct_0('#skF_4')) | ~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_179, c_202])).
% 3.10/1.45  tff(c_274, plain, (![E_205, D_206]: (k1_funct_1(E_205, '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206))!=k1_funct_1('#skF_7', '#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206)) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_206)=E_205 | ~m1_subset_1(E_205, k1_zfmisc_1(k2_zfmisc_1(D_206, u1_struct_0('#skF_3')))) | ~v1_funct_2(E_205, D_206, u1_struct_0('#skF_3')) | ~v1_funct_1(E_205) | ~m1_subset_1(D_206, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(D_206) | ~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), E_205, D_206), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_244, c_203])).
% 3.10/1.45  tff(c_277, plain, (![D_206]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_206)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(D_206, u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', D_206, u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_206, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(D_206) | ~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', D_206), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', D_206), u1_struct_0('#skF_4')))), inference(reflexivity, [status(thm), theory('equality')], [c_274])).
% 3.10/1.45  tff(c_281, plain, (![D_222]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', D_222)='#skF_7' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(D_222, u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', D_222, u1_struct_0('#skF_3')) | ~m1_subset_1(D_222, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(D_222) | ~r2_hidden('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', D_222), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', D_222), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_277])).
% 3.10/1.45  tff(c_285, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_271, c_281])).
% 3.10/1.45  tff(c_288, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_30, c_28, c_285])).
% 3.10/1.45  tff(c_289, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_244, c_196, c_288])).
% 3.10/1.45  tff(c_290, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_289])).
% 3.10/1.45  tff(c_293, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_290])).
% 3.10/1.45  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_293])).
% 3.10/1.45  tff(c_299, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_289])).
% 3.10/1.45  tff(c_195, plain, (![C_189, A_190]: (m1_subset_1('#skF_2'(C_189, A_190, u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), A_190) | k2_partfun1(A_190, u1_struct_0('#skF_3'), C_189, u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_190)) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_190, u1_struct_0('#skF_3')))) | ~v1_funct_2(C_189, A_190, u1_struct_0('#skF_3')) | ~v1_funct_1(C_189) | v1_xboole_0(A_190))), inference(splitRight, [status(thm)], [c_178])).
% 3.10/1.45  tff(c_298, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_4')) | k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7'), inference(splitRight, [status(thm)], [c_289])).
% 3.10/1.45  tff(c_310, plain, (~m1_subset_1('#skF_2'('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5')), u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_298])).
% 3.10/1.45  tff(c_313, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7' | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_195, c_310])).
% 3.10/1.45  tff(c_316, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7' | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_299, c_313])).
% 3.10/1.45  tff(c_317, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_244, c_316])).
% 3.10/1.45  tff(c_46, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_52, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_119, plain, (![A_184, B_185, C_186, D_187]: (k2_partfun1(u1_struct_0(A_184), u1_struct_0(B_185), C_186, u1_struct_0(D_187))=k2_tmap_1(A_184, B_185, C_186, D_187) | ~m1_pre_topc(D_187, A_184) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184), u1_struct_0(B_185)))) | ~v1_funct_2(C_186, u1_struct_0(A_184), u1_struct_0(B_185)) | ~v1_funct_1(C_186) | ~l1_pre_topc(B_185) | ~v2_pre_topc(B_185) | v2_struct_0(B_185) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.10/1.45  tff(c_123, plain, (![D_187]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_187))=k2_tmap_1('#skF_4', '#skF_3', '#skF_6', D_187) | ~m1_pre_topc(D_187, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_119])).
% 3.10/1.45  tff(c_130, plain, (![D_187]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_187))=k2_tmap_1('#skF_4', '#skF_3', '#skF_6', D_187) | ~m1_pre_topc(D_187, '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_52, c_50, c_38, c_36, c_123])).
% 3.10/1.45  tff(c_131, plain, (![D_187]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0(D_187))=k2_tmap_1('#skF_4', '#skF_3', '#skF_6', D_187) | ~m1_pre_topc(D_187, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_54, c_130])).
% 3.10/1.45  tff(c_321, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5')='#skF_7' | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_317, c_131])).
% 3.10/1.45  tff(c_328, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_321])).
% 3.10/1.45  tff(c_24, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_179])).
% 3.10/1.45  tff(c_332, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_328, c_24])).
% 3.10/1.45  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_332])).
% 3.10/1.45  tff(c_336, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'), '#skF_6', u1_struct_0('#skF_5'))='#skF_7'), inference(splitRight, [status(thm)], [c_298])).
% 3.10/1.45  tff(c_348, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5')='#skF_7' | ~m1_pre_topc('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_336, c_131])).
% 3.10/1.45  tff(c_355, plain, (k2_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_348])).
% 3.10/1.45  tff(c_359, plain, (~r2_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_24])).
% 3.10/1.45  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_114, c_359])).
% 3.10/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.45  
% 3.10/1.45  Inference rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Ref     : 2
% 3.10/1.45  #Sup     : 53
% 3.10/1.45  #Fact    : 0
% 3.10/1.45  #Define  : 0
% 3.10/1.45  #Split   : 6
% 3.10/1.45  #Chain   : 0
% 3.10/1.45  #Close   : 0
% 3.10/1.45  
% 3.10/1.45  Ordering : KBO
% 3.10/1.45  
% 3.10/1.45  Simplification rules
% 3.10/1.45  ----------------------
% 3.10/1.45  #Subsume      : 0
% 3.10/1.45  #Demod        : 62
% 3.10/1.45  #Tautology    : 10
% 3.10/1.45  #SimpNegUnit  : 12
% 3.10/1.45  #BackRed      : 2
% 3.10/1.45  
% 3.10/1.45  #Partial instantiations: 0
% 3.10/1.45  #Strategies tried      : 1
% 3.10/1.45  
% 3.10/1.45  Timing (in seconds)
% 3.10/1.45  ----------------------
% 3.10/1.45  Preprocessing        : 0.35
% 3.10/1.45  Parsing              : 0.19
% 3.10/1.45  CNF conversion       : 0.04
% 3.10/1.45  Main loop            : 0.32
% 3.10/1.45  Inferencing          : 0.12
% 3.10/1.45  Reduction            : 0.10
% 3.10/1.45  Demodulation         : 0.07
% 3.10/1.45  BG Simplification    : 0.02
% 3.10/1.45  Subsumption          : 0.06
% 3.10/1.45  Abstraction          : 0.02
% 3.10/1.45  MUC search           : 0.00
% 3.10/1.45  Cooper               : 0.00
% 3.10/1.45  Total                : 0.71
% 3.10/1.45  Index Insertion      : 0.00
% 3.10/1.45  Index Deletion       : 0.00
% 3.10/1.45  Index Matching       : 0.00
% 3.10/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
