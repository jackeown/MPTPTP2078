%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:29 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 472 expanded)
%              Number of leaves         :   34 ( 204 expanded)
%              Depth                    :   20
%              Number of atoms          :  353 (3547 expanded)
%              Number of equality atoms :    8 ( 368 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_199,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k1_tsep_1(A,B,C)))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ( ( E = D
                                & F = D )
                             => ! [G] :
                                  ( m1_connsp_2(G,B,E)
                                 => ! [H] :
                                      ( m1_connsp_2(H,C,F)
                                     => ? [I] :
                                          ( m1_connsp_2(I,k1_tsep_1(A,B,C),D)
                                          & r1_tarski(I,k2_xboole_0(G,H)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_tmap_1)).

tff(f_155,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(k1_tsep_1(A,B,C)))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ( ( E = D
                              & F = D )
                           => ! [G] :
                                ( m1_connsp_2(G,B,E)
                               => ! [H] :
                                    ( m1_connsp_2(H,C,F)
                                   => ? [I] :
                                        ( m1_subset_1(I,k1_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C))))
                                        & v3_pre_topc(I,k1_tsep_1(A,B,C))
                                        & r2_hidden(D,I)
                                        & r1_tarski(I,k2_xboole_0(G,H)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tmap_1)).

tff(f_84,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & v2_pre_topc(k1_tsep_1(A,B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_46,plain,(
    '#skF_6' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_71,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_54])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_69,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52])).

tff(c_72,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_69])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_70,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_44,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_73,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_44])).

tff(c_42,plain,(
    m1_connsp_2('#skF_10','#skF_5','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_32,plain,(
    ! [H_542,C_418,A_34,G_538,B_290,F_530] :
      ( r1_tarski('#skF_2'(A_34,F_530,H_542,G_538,F_530,F_530,C_418,B_290),k2_xboole_0(G_538,H_542))
      | ~ m1_connsp_2(H_542,C_418,F_530)
      | ~ m1_connsp_2(G_538,B_290,F_530)
      | ~ m1_subset_1(F_530,u1_struct_0(C_418))
      | ~ m1_subset_1(F_530,u1_struct_0(B_290))
      | ~ m1_subset_1(F_530,u1_struct_0(k1_tsep_1(A_34,B_290,C_418)))
      | ~ m1_pre_topc(C_418,A_34)
      | v2_struct_0(C_418)
      | ~ m1_pre_topc(B_290,A_34)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_36,plain,(
    ! [H_542,C_418,A_34,G_538,B_290,F_530] :
      ( v3_pre_topc('#skF_2'(A_34,F_530,H_542,G_538,F_530,F_530,C_418,B_290),k1_tsep_1(A_34,B_290,C_418))
      | ~ m1_connsp_2(H_542,C_418,F_530)
      | ~ m1_connsp_2(G_538,B_290,F_530)
      | ~ m1_subset_1(F_530,u1_struct_0(C_418))
      | ~ m1_subset_1(F_530,u1_struct_0(B_290))
      | ~ m1_subset_1(F_530,u1_struct_0(k1_tsep_1(A_34,B_290,C_418)))
      | ~ m1_pre_topc(C_418,A_34)
      | v2_struct_0(C_418)
      | ~ m1_pre_topc(B_290,A_34)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_108,plain,(
    ! [A_1059,B_1060,C_1061] :
      ( m1_pre_topc(k1_tsep_1(A_1059,B_1060,C_1061),A_1059)
      | ~ m1_pre_topc(C_1061,A_1059)
      | v2_struct_0(C_1061)
      | ~ m1_pre_topc(B_1060,A_1059)
      | v2_struct_0(B_1060)
      | ~ l1_pre_topc(A_1059)
      | v2_struct_0(A_1059) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( l1_pre_topc(B_5)
      | ~ m1_pre_topc(B_5,A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_112,plain,(
    ! [A_1059,B_1060,C_1061] :
      ( l1_pre_topc(k1_tsep_1(A_1059,B_1060,C_1061))
      | ~ m1_pre_topc(C_1061,A_1059)
      | v2_struct_0(C_1061)
      | ~ m1_pre_topc(B_1060,A_1059)
      | v2_struct_0(B_1060)
      | ~ l1_pre_topc(A_1059)
      | v2_struct_0(A_1059) ) ),
    inference(resolution,[status(thm)],[c_108,c_8])).

tff(c_26,plain,(
    ! [A_31,B_32,C_33] :
      ( v2_pre_topc(k1_tsep_1(A_31,B_32,C_33))
      | ~ m1_pre_topc(C_33,A_31)
      | v2_struct_0(C_33)
      | ~ m1_pre_topc(B_32,A_31)
      | v2_struct_0(B_32)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    ! [H_542,C_418,A_34,G_538,B_290,F_530] :
      ( m1_subset_1('#skF_2'(A_34,F_530,H_542,G_538,F_530,F_530,C_418,B_290),k1_zfmisc_1(u1_struct_0(k1_tsep_1(A_34,B_290,C_418))))
      | ~ m1_connsp_2(H_542,C_418,F_530)
      | ~ m1_connsp_2(G_538,B_290,F_530)
      | ~ m1_subset_1(F_530,u1_struct_0(C_418))
      | ~ m1_subset_1(F_530,u1_struct_0(B_290))
      | ~ m1_subset_1(F_530,u1_struct_0(k1_tsep_1(A_34,B_290,C_418)))
      | ~ m1_pre_topc(C_418,A_34)
      | v2_struct_0(C_418)
      | ~ m1_pre_topc(B_290,A_34)
      | v2_struct_0(B_290)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_1096,F_1099,G_1098,C_1100,B_1101,H_1097] :
      ( r2_hidden(F_1099,'#skF_2'(A_1096,F_1099,H_1097,G_1098,F_1099,F_1099,C_1100,B_1101))
      | ~ m1_connsp_2(H_1097,C_1100,F_1099)
      | ~ m1_connsp_2(G_1098,B_1101,F_1099)
      | ~ m1_subset_1(F_1099,u1_struct_0(C_1100))
      | ~ m1_subset_1(F_1099,u1_struct_0(B_1101))
      | ~ m1_subset_1(F_1099,u1_struct_0(k1_tsep_1(A_1096,B_1101,C_1100)))
      | ~ m1_pre_topc(C_1100,A_1096)
      | v2_struct_0(C_1100)
      | ~ m1_pre_topc(B_1101,A_1096)
      | v2_struct_0(B_1101)
      | ~ l1_pre_topc(A_1096)
      | ~ v2_pre_topc(A_1096)
      | v2_struct_0(A_1096) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_140,plain,(
    ! [H_1097,G_1098] :
      ( r2_hidden('#skF_8','#skF_2'('#skF_3','#skF_8',H_1097,G_1098,'#skF_8','#skF_8','#skF_5','#skF_4'))
      | ~ m1_connsp_2(H_1097,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1098,'#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_71,c_138])).

tff(c_143,plain,(
    ! [H_1097,G_1098] :
      ( r2_hidden('#skF_8','#skF_2'('#skF_3','#skF_8',H_1097,G_1098,'#skF_8','#skF_8','#skF_5','#skF_4'))
      | ~ m1_connsp_2(H_1097,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1098,'#skF_4','#skF_8')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_72,c_50,c_140])).

tff(c_145,plain,(
    ! [H_1102,G_1103] :
      ( r2_hidden('#skF_8','#skF_2'('#skF_3','#skF_8',H_1102,G_1103,'#skF_8','#skF_8','#skF_5','#skF_4'))
      | ~ m1_connsp_2(H_1102,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1103,'#skF_4','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_143])).

tff(c_10,plain,(
    ! [C_24,A_6,B_18,D_27] :
      ( m1_connsp_2(C_24,A_6,B_18)
      | ~ r2_hidden(B_18,D_27)
      | ~ r1_tarski(D_27,C_24)
      | ~ v3_pre_topc(D_27,A_6)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_18,u1_struct_0(A_6))
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_165,plain,(
    ! [C_1126,A_1127,H_1128,G_1129] :
      ( m1_connsp_2(C_1126,A_1127,'#skF_8')
      | ~ r1_tarski('#skF_2'('#skF_3','#skF_8',H_1128,G_1129,'#skF_8','#skF_8','#skF_5','#skF_4'),C_1126)
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_1128,G_1129,'#skF_8','#skF_8','#skF_5','#skF_4'),A_1127)
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_8',H_1128,G_1129,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0(A_1127)))
      | ~ m1_subset_1(C_1126,k1_zfmisc_1(u1_struct_0(A_1127)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_1127))
      | ~ l1_pre_topc(A_1127)
      | ~ v2_pre_topc(A_1127)
      | v2_struct_0(A_1127)
      | ~ m1_connsp_2(H_1128,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1129,'#skF_4','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_145,c_10])).

tff(c_177,plain,(
    ! [H_1130,G_1131,A_1132] :
      ( m1_connsp_2('#skF_2'('#skF_3','#skF_8',H_1130,G_1131,'#skF_8','#skF_8','#skF_5','#skF_4'),A_1132,'#skF_8')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_1130,G_1131,'#skF_8','#skF_8','#skF_5','#skF_4'),A_1132)
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_8',H_1130,G_1131,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_zfmisc_1(u1_struct_0(A_1132)))
      | ~ m1_subset_1('#skF_8',u1_struct_0(A_1132))
      | ~ l1_pre_topc(A_1132)
      | ~ v2_pre_topc(A_1132)
      | v2_struct_0(A_1132)
      | ~ m1_connsp_2(H_1130,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1131,'#skF_4','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_6,c_165])).

tff(c_181,plain,(
    ! [H_542,G_538] :
      ( m1_connsp_2('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_8')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_connsp_2(H_542,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_538,'#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_177])).

tff(c_184,plain,(
    ! [H_542,G_538] :
      ( m1_connsp_2('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_8')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_connsp_2(H_542,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_538,'#skF_4','#skF_8')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_71,c_72,c_50,c_181])).

tff(c_185,plain,(
    ! [H_542,G_538] :
      ( m1_connsp_2('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_8')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ v2_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_connsp_2(H_542,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_538,'#skF_4','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_184])).

tff(c_186,plain,(
    ~ v2_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_189,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_186])).

tff(c_192,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_189])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_192])).

tff(c_195,plain,(
    ! [H_542,G_538] :
      ( ~ l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | m1_connsp_2('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_8')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_connsp_2(H_542,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_538,'#skF_4','#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_197,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_201,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_112,c_197])).

tff(c_204,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_56,c_201])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_204])).

tff(c_207,plain,(
    ! [H_542,G_538] :
      ( v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | m1_connsp_2('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_8')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_connsp_2(H_542,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_538,'#skF_4','#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_209,plain,(
    v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_24,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ v2_struct_0(k1_tsep_1(A_28,B_29,C_30))
      | ~ m1_pre_topc(C_30,A_28)
      | v2_struct_0(C_30)
      | ~ m1_pre_topc(B_29,A_28)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_213,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_209,c_24])).

tff(c_216,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_56,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_216])).

tff(c_221,plain,(
    ! [H_1142,G_1143] :
      ( m1_connsp_2('#skF_2'('#skF_3','#skF_8',H_1142,G_1143,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_8')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_1142,G_1143,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_connsp_2(H_1142,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1143,'#skF_4','#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_40,plain,(
    ! [I_1046] :
      ( ~ r1_tarski(I_1046,k2_xboole_0('#skF_9','#skF_10'))
      | ~ m1_connsp_2(I_1046,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_74,plain,(
    ! [I_1046] :
      ( ~ r1_tarski(I_1046,k2_xboole_0('#skF_9','#skF_10'))
      | ~ m1_connsp_2(I_1046,k1_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40])).

tff(c_226,plain,(
    ! [H_1144,G_1145] :
      ( ~ r1_tarski('#skF_2'('#skF_3','#skF_8',H_1144,G_1145,'#skF_8','#skF_8','#skF_5','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_8',H_1144,G_1145,'#skF_8','#skF_8','#skF_5','#skF_4'),k1_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_connsp_2(H_1144,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1145,'#skF_4','#skF_8') ) ),
    inference(resolution,[status(thm)],[c_221,c_74])).

tff(c_230,plain,(
    ! [H_542,G_538] :
      ( ~ r1_tarski('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ m1_connsp_2(H_542,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_538,'#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_226])).

tff(c_233,plain,(
    ! [H_542,G_538] :
      ( ~ r1_tarski('#skF_2'('#skF_3','#skF_8',H_542,G_538,'#skF_8','#skF_8','#skF_5','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ m1_connsp_2(H_542,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_538,'#skF_4','#skF_8')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_71,c_72,c_50,c_230])).

tff(c_235,plain,(
    ! [H_1146,G_1147] :
      ( ~ r1_tarski('#skF_2'('#skF_3','#skF_8',H_1146,G_1147,'#skF_8','#skF_8','#skF_5','#skF_4'),k2_xboole_0('#skF_9','#skF_10'))
      | ~ m1_connsp_2(H_1146,'#skF_5','#skF_8')
      | ~ m1_connsp_2(G_1147,'#skF_4','#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_233])).

tff(c_239,plain,
    ( ~ m1_connsp_2('#skF_10','#skF_5','#skF_8')
    | ~ m1_connsp_2('#skF_9','#skF_4','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_5')))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_235])).

tff(c_242,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_56,c_71,c_72,c_50,c_73,c_42,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_58,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:51:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.39  
% 2.97/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.40  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 2.97/1.40  
% 2.97/1.40  %Foreground sorts:
% 2.97/1.40  
% 2.97/1.40  
% 2.97/1.40  %Background operators:
% 2.97/1.40  
% 2.97/1.40  
% 2.97/1.40  %Foreground operators:
% 2.97/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.97/1.40  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.97/1.40  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 2.97/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.97/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.97/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.97/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.97/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.40  tff('#skF_10', type, '#skF_10': $i).
% 2.97/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.97/1.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.97/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.97/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.40  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.97/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.97/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.40  
% 3.11/1.42  tff(f_199, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (m1_subset_1(D, u1_struct_0(k1_tsep_1(A, B, C))) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (((E = D) & (F = D)) => (![G]: (m1_connsp_2(G, B, E) => (![H]: (m1_connsp_2(H, C, F) => (?[I]: (m1_connsp_2(I, k1_tsep_1(A, B, C), D) & r1_tarski(I, k2_xboole_0(G, H))))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_tmap_1)).
% 3.11/1.42  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (m1_subset_1(D, u1_struct_0(k1_tsep_1(A, B, C))) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (((E = D) & (F = D)) => (![G]: (m1_connsp_2(G, B, E) => (![H]: (m1_connsp_2(H, C, F) => (?[I]: (((m1_subset_1(I, k1_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)))) & v3_pre_topc(I, k1_tsep_1(A, B, C))) & r2_hidden(D, I)) & r1_tarski(I, k2_xboole_0(G, H))))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tmap_1)).
% 3.11/1.42  tff(f_84, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 3.11/1.42  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.11/1.42  tff(f_108, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & v2_pre_topc(k1_tsep_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tmap_1)).
% 3.11/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.11/1.42  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 3.11/1.42  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_46, plain, ('#skF_6'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_54, plain, (m1_subset_1('#skF_6', u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_71, plain, (m1_subset_1('#skF_8', u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_54])).
% 3.11/1.42  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_69, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52])).
% 3.11/1.42  tff(c_72, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_69])).
% 3.11/1.42  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_70, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 3.11/1.42  tff(c_44, plain, (m1_connsp_2('#skF_9', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_73, plain, (m1_connsp_2('#skF_9', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_44])).
% 3.11/1.42  tff(c_42, plain, (m1_connsp_2('#skF_10', '#skF_5', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_32, plain, (![H_542, C_418, A_34, G_538, B_290, F_530]: (r1_tarski('#skF_2'(A_34, F_530, H_542, G_538, F_530, F_530, C_418, B_290), k2_xboole_0(G_538, H_542)) | ~m1_connsp_2(H_542, C_418, F_530) | ~m1_connsp_2(G_538, B_290, F_530) | ~m1_subset_1(F_530, u1_struct_0(C_418)) | ~m1_subset_1(F_530, u1_struct_0(B_290)) | ~m1_subset_1(F_530, u1_struct_0(k1_tsep_1(A_34, B_290, C_418))) | ~m1_pre_topc(C_418, A_34) | v2_struct_0(C_418) | ~m1_pre_topc(B_290, A_34) | v2_struct_0(B_290) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.11/1.42  tff(c_36, plain, (![H_542, C_418, A_34, G_538, B_290, F_530]: (v3_pre_topc('#skF_2'(A_34, F_530, H_542, G_538, F_530, F_530, C_418, B_290), k1_tsep_1(A_34, B_290, C_418)) | ~m1_connsp_2(H_542, C_418, F_530) | ~m1_connsp_2(G_538, B_290, F_530) | ~m1_subset_1(F_530, u1_struct_0(C_418)) | ~m1_subset_1(F_530, u1_struct_0(B_290)) | ~m1_subset_1(F_530, u1_struct_0(k1_tsep_1(A_34, B_290, C_418))) | ~m1_pre_topc(C_418, A_34) | v2_struct_0(C_418) | ~m1_pre_topc(B_290, A_34) | v2_struct_0(B_290) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.11/1.42  tff(c_108, plain, (![A_1059, B_1060, C_1061]: (m1_pre_topc(k1_tsep_1(A_1059, B_1060, C_1061), A_1059) | ~m1_pre_topc(C_1061, A_1059) | v2_struct_0(C_1061) | ~m1_pre_topc(B_1060, A_1059) | v2_struct_0(B_1060) | ~l1_pre_topc(A_1059) | v2_struct_0(A_1059))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.11/1.42  tff(c_8, plain, (![B_5, A_3]: (l1_pre_topc(B_5) | ~m1_pre_topc(B_5, A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.11/1.42  tff(c_112, plain, (![A_1059, B_1060, C_1061]: (l1_pre_topc(k1_tsep_1(A_1059, B_1060, C_1061)) | ~m1_pre_topc(C_1061, A_1059) | v2_struct_0(C_1061) | ~m1_pre_topc(B_1060, A_1059) | v2_struct_0(B_1060) | ~l1_pre_topc(A_1059) | v2_struct_0(A_1059))), inference(resolution, [status(thm)], [c_108, c_8])).
% 3.11/1.42  tff(c_26, plain, (![A_31, B_32, C_33]: (v2_pre_topc(k1_tsep_1(A_31, B_32, C_33)) | ~m1_pre_topc(C_33, A_31) | v2_struct_0(C_33) | ~m1_pre_topc(B_32, A_31) | v2_struct_0(B_32) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.11/1.42  tff(c_38, plain, (![H_542, C_418, A_34, G_538, B_290, F_530]: (m1_subset_1('#skF_2'(A_34, F_530, H_542, G_538, F_530, F_530, C_418, B_290), k1_zfmisc_1(u1_struct_0(k1_tsep_1(A_34, B_290, C_418)))) | ~m1_connsp_2(H_542, C_418, F_530) | ~m1_connsp_2(G_538, B_290, F_530) | ~m1_subset_1(F_530, u1_struct_0(C_418)) | ~m1_subset_1(F_530, u1_struct_0(B_290)) | ~m1_subset_1(F_530, u1_struct_0(k1_tsep_1(A_34, B_290, C_418))) | ~m1_pre_topc(C_418, A_34) | v2_struct_0(C_418) | ~m1_pre_topc(B_290, A_34) | v2_struct_0(B_290) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.11/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.11/1.42  tff(c_138, plain, (![A_1096, F_1099, G_1098, C_1100, B_1101, H_1097]: (r2_hidden(F_1099, '#skF_2'(A_1096, F_1099, H_1097, G_1098, F_1099, F_1099, C_1100, B_1101)) | ~m1_connsp_2(H_1097, C_1100, F_1099) | ~m1_connsp_2(G_1098, B_1101, F_1099) | ~m1_subset_1(F_1099, u1_struct_0(C_1100)) | ~m1_subset_1(F_1099, u1_struct_0(B_1101)) | ~m1_subset_1(F_1099, u1_struct_0(k1_tsep_1(A_1096, B_1101, C_1100))) | ~m1_pre_topc(C_1100, A_1096) | v2_struct_0(C_1100) | ~m1_pre_topc(B_1101, A_1096) | v2_struct_0(B_1101) | ~l1_pre_topc(A_1096) | ~v2_pre_topc(A_1096) | v2_struct_0(A_1096))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.11/1.42  tff(c_140, plain, (![H_1097, G_1098]: (r2_hidden('#skF_8', '#skF_2'('#skF_3', '#skF_8', H_1097, G_1098, '#skF_8', '#skF_8', '#skF_5', '#skF_4')) | ~m1_connsp_2(H_1097, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1098, '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_71, c_138])).
% 3.11/1.42  tff(c_143, plain, (![H_1097, G_1098]: (r2_hidden('#skF_8', '#skF_2'('#skF_3', '#skF_8', H_1097, G_1098, '#skF_8', '#skF_8', '#skF_5', '#skF_4')) | ~m1_connsp_2(H_1097, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1098, '#skF_4', '#skF_8') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_72, c_50, c_140])).
% 3.11/1.42  tff(c_145, plain, (![H_1102, G_1103]: (r2_hidden('#skF_8', '#skF_2'('#skF_3', '#skF_8', H_1102, G_1103, '#skF_8', '#skF_8', '#skF_5', '#skF_4')) | ~m1_connsp_2(H_1102, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1103, '#skF_4', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_143])).
% 3.11/1.42  tff(c_10, plain, (![C_24, A_6, B_18, D_27]: (m1_connsp_2(C_24, A_6, B_18) | ~r2_hidden(B_18, D_27) | ~r1_tarski(D_27, C_24) | ~v3_pre_topc(D_27, A_6) | ~m1_subset_1(D_27, k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(C_24, k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_18, u1_struct_0(A_6)) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.11/1.42  tff(c_165, plain, (![C_1126, A_1127, H_1128, G_1129]: (m1_connsp_2(C_1126, A_1127, '#skF_8') | ~r1_tarski('#skF_2'('#skF_3', '#skF_8', H_1128, G_1129, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), C_1126) | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_1128, G_1129, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), A_1127) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_8', H_1128, G_1129, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_1127))) | ~m1_subset_1(C_1126, k1_zfmisc_1(u1_struct_0(A_1127))) | ~m1_subset_1('#skF_8', u1_struct_0(A_1127)) | ~l1_pre_topc(A_1127) | ~v2_pre_topc(A_1127) | v2_struct_0(A_1127) | ~m1_connsp_2(H_1128, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1129, '#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_145, c_10])).
% 3.11/1.42  tff(c_177, plain, (![H_1130, G_1131, A_1132]: (m1_connsp_2('#skF_2'('#skF_3', '#skF_8', H_1130, G_1131, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), A_1132, '#skF_8') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_1130, G_1131, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), A_1132) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_8', H_1130, G_1131, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_zfmisc_1(u1_struct_0(A_1132))) | ~m1_subset_1('#skF_8', u1_struct_0(A_1132)) | ~l1_pre_topc(A_1132) | ~v2_pre_topc(A_1132) | v2_struct_0(A_1132) | ~m1_connsp_2(H_1130, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1131, '#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_6, c_165])).
% 3.11/1.42  tff(c_181, plain, (![H_542, G_538]: (m1_connsp_2('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2(H_542, '#skF_5', '#skF_8') | ~m1_connsp_2(G_538, '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_177])).
% 3.11/1.42  tff(c_184, plain, (![H_542, G_538]: (m1_connsp_2('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2(H_542, '#skF_5', '#skF_8') | ~m1_connsp_2(G_538, '#skF_4', '#skF_8') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_71, c_72, c_50, c_181])).
% 3.11/1.42  tff(c_185, plain, (![H_542, G_538]: (m1_connsp_2('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~v2_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2(H_542, '#skF_5', '#skF_8') | ~m1_connsp_2(G_538, '#skF_4', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_184])).
% 3.11/1.42  tff(c_186, plain, (~v2_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_185])).
% 3.11/1.42  tff(c_189, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_26, c_186])).
% 3.11/1.42  tff(c_192, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_189])).
% 3.11/1.42  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_192])).
% 3.11/1.42  tff(c_195, plain, (![H_542, G_538]: (~l1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | m1_connsp_2('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2(H_542, '#skF_5', '#skF_8') | ~m1_connsp_2(G_538, '#skF_4', '#skF_8'))), inference(splitRight, [status(thm)], [c_185])).
% 3.11/1.42  tff(c_197, plain, (~l1_pre_topc(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_195])).
% 3.11/1.42  tff(c_201, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_112, c_197])).
% 3.11/1.42  tff(c_204, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_56, c_201])).
% 3.11/1.42  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_204])).
% 3.11/1.42  tff(c_207, plain, (![H_542, G_538]: (v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | m1_connsp_2('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2(H_542, '#skF_5', '#skF_8') | ~m1_connsp_2(G_538, '#skF_4', '#skF_8'))), inference(splitRight, [status(thm)], [c_195])).
% 3.11/1.42  tff(c_209, plain, (v2_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_207])).
% 3.11/1.42  tff(c_24, plain, (![A_28, B_29, C_30]: (~v2_struct_0(k1_tsep_1(A_28, B_29, C_30)) | ~m1_pre_topc(C_30, A_28) | v2_struct_0(C_30) | ~m1_pre_topc(B_29, A_28) | v2_struct_0(B_29) | ~l1_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.11/1.42  tff(c_213, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_209, c_24])).
% 3.11/1.42  tff(c_216, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_56, c_213])).
% 3.11/1.42  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_216])).
% 3.11/1.42  tff(c_221, plain, (![H_1142, G_1143]: (m1_connsp_2('#skF_2'('#skF_3', '#skF_8', H_1142, G_1143, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_8') | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_1142, G_1143, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2(H_1142, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1143, '#skF_4', '#skF_8'))), inference(splitRight, [status(thm)], [c_207])).
% 3.11/1.42  tff(c_40, plain, (![I_1046]: (~r1_tarski(I_1046, k2_xboole_0('#skF_9', '#skF_10')) | ~m1_connsp_2(I_1046, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_199])).
% 3.11/1.42  tff(c_74, plain, (![I_1046]: (~r1_tarski(I_1046, k2_xboole_0('#skF_9', '#skF_10')) | ~m1_connsp_2(I_1046, k1_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40])).
% 3.11/1.42  tff(c_226, plain, (![H_1144, G_1145]: (~r1_tarski('#skF_2'('#skF_3', '#skF_8', H_1144, G_1145, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k2_xboole_0('#skF_9', '#skF_10')) | ~v3_pre_topc('#skF_2'('#skF_3', '#skF_8', H_1144, G_1145, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k1_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_connsp_2(H_1144, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1145, '#skF_4', '#skF_8'))), inference(resolution, [status(thm)], [c_221, c_74])).
% 3.11/1.42  tff(c_230, plain, (![H_542, G_538]: (~r1_tarski('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k2_xboole_0('#skF_9', '#skF_10')) | ~m1_connsp_2(H_542, '#skF_5', '#skF_8') | ~m1_connsp_2(G_538, '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_226])).
% 3.11/1.42  tff(c_233, plain, (![H_542, G_538]: (~r1_tarski('#skF_2'('#skF_3', '#skF_8', H_542, G_538, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k2_xboole_0('#skF_9', '#skF_10')) | ~m1_connsp_2(H_542, '#skF_5', '#skF_8') | ~m1_connsp_2(G_538, '#skF_4', '#skF_8') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_71, c_72, c_50, c_230])).
% 3.11/1.42  tff(c_235, plain, (![H_1146, G_1147]: (~r1_tarski('#skF_2'('#skF_3', '#skF_8', H_1146, G_1147, '#skF_8', '#skF_8', '#skF_5', '#skF_4'), k2_xboole_0('#skF_9', '#skF_10')) | ~m1_connsp_2(H_1146, '#skF_5', '#skF_8') | ~m1_connsp_2(G_1147, '#skF_4', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_233])).
% 3.11/1.42  tff(c_239, plain, (~m1_connsp_2('#skF_10', '#skF_5', '#skF_8') | ~m1_connsp_2('#skF_9', '#skF_4', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0(k1_tsep_1('#skF_3', '#skF_4', '#skF_5'))) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_235])).
% 3.11/1.42  tff(c_242, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_56, c_71, c_72, c_50, c_73, c_42, c_239])).
% 3.11/1.42  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_58, c_242])).
% 3.11/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.42  
% 3.11/1.42  Inference rules
% 3.11/1.42  ----------------------
% 3.11/1.42  #Ref     : 0
% 3.11/1.42  #Sup     : 28
% 3.11/1.42  #Fact    : 0
% 3.11/1.42  #Define  : 0
% 3.11/1.42  #Split   : 3
% 3.11/1.42  #Chain   : 0
% 3.11/1.42  #Close   : 0
% 3.11/1.42  
% 3.11/1.42  Ordering : KBO
% 3.11/1.42  
% 3.11/1.42  Simplification rules
% 3.11/1.42  ----------------------
% 3.11/1.42  #Subsume      : 3
% 3.11/1.42  #Demod        : 56
% 3.11/1.42  #Tautology    : 6
% 3.11/1.42  #SimpNegUnit  : 8
% 3.11/1.42  #BackRed      : 0
% 3.11/1.42  
% 3.11/1.42  #Partial instantiations: 0
% 3.11/1.42  #Strategies tried      : 1
% 3.11/1.42  
% 3.11/1.42  Timing (in seconds)
% 3.11/1.42  ----------------------
% 3.11/1.42  Preprocessing        : 0.39
% 3.11/1.42  Parsing              : 0.19
% 3.11/1.42  CNF conversion       : 0.06
% 3.11/1.42  Main loop            : 0.28
% 3.11/1.42  Inferencing          : 0.10
% 3.11/1.42  Reduction            : 0.08
% 3.11/1.42  Demodulation         : 0.06
% 3.11/1.42  BG Simplification    : 0.02
% 3.11/1.42  Subsumption          : 0.06
% 3.11/1.42  Abstraction          : 0.01
% 3.11/1.42  MUC search           : 0.00
% 3.11/1.42  Cooper               : 0.00
% 3.11/1.42  Total                : 0.70
% 3.11/1.42  Index Insertion      : 0.00
% 3.11/1.42  Index Deletion       : 0.00
% 3.11/1.42  Index Matching       : 0.00
% 3.11/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
