%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:26 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :  213 (1041 expanded)
%              Number of leaves         :   35 ( 381 expanded)
%              Depth                    :   19
%              Number of atoms          :  870 (8341 expanded)
%              Number of equality atoms :    4 ( 288 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,B)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,A,E,G)
                                        <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_158,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_30,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_24,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_60,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_40,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_79,plain,(
    ! [B_547,A_548] :
      ( l1_pre_topc(B_547)
      | ~ m1_pre_topc(B_547,A_548)
      | ~ l1_pre_topc(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_79])).

tff(c_95,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_88])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_161,plain,(
    ! [C_561,A_562,B_563] :
      ( m1_subset_1(C_561,k1_zfmisc_1(u1_struct_0(A_562)))
      | ~ m1_subset_1(C_561,k1_zfmisc_1(u1_struct_0(B_563)))
      | ~ m1_pre_topc(B_563,A_562)
      | ~ l1_pre_topc(A_562) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_178,plain,(
    ! [A_566,A_567,B_568] :
      ( m1_subset_1(A_566,k1_zfmisc_1(u1_struct_0(A_567)))
      | ~ m1_pre_topc(B_568,A_567)
      | ~ l1_pre_topc(A_567)
      | ~ r1_tarski(A_566,u1_struct_0(B_568)) ) ),
    inference(resolution,[status(thm)],[c_4,c_161])).

tff(c_184,plain,(
    ! [A_566] :
      ( m1_subset_1(A_566,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_566,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_178])).

tff(c_193,plain,(
    ! [A_566] :
      ( m1_subset_1(A_566,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_566,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_184])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_22,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_72,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_64])).

tff(c_112,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_73,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_32])).

tff(c_70,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_71,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_70])).

tff(c_160,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_71])).

tff(c_415,plain,(
    ! [E_601,A_599,B_598,D_597,C_596,H_600,F_602] :
      ( r1_tmap_1(D_597,B_598,E_601,H_600)
      | ~ r1_tmap_1(C_596,B_598,k3_tmap_1(A_599,B_598,D_597,C_596,E_601),H_600)
      | ~ m1_connsp_2(F_602,D_597,H_600)
      | ~ r1_tarski(F_602,u1_struct_0(C_596))
      | ~ m1_subset_1(H_600,u1_struct_0(C_596))
      | ~ m1_subset_1(H_600,u1_struct_0(D_597))
      | ~ m1_subset_1(F_602,k1_zfmisc_1(u1_struct_0(D_597)))
      | ~ m1_pre_topc(C_596,D_597)
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_597),u1_struct_0(B_598))))
      | ~ v1_funct_2(E_601,u1_struct_0(D_597),u1_struct_0(B_598))
      | ~ v1_funct_1(E_601)
      | ~ m1_pre_topc(D_597,A_599)
      | v2_struct_0(D_597)
      | ~ m1_pre_topc(C_596,A_599)
      | v2_struct_0(C_596)
      | ~ l1_pre_topc(B_598)
      | ~ v2_pre_topc(B_598)
      | v2_struct_0(B_598)
      | ~ l1_pre_topc(A_599)
      | ~ v2_pre_topc(A_599)
      | v2_struct_0(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_417,plain,(
    ! [F_602] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_602,'#skF_4','#skF_8')
      | ~ r1_tarski(F_602,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_602,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_160,c_415])).

tff(c_420,plain,(
    ! [F_602] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ m1_connsp_2(F_602,'#skF_4','#skF_8')
      | ~ r1_tarski(F_602,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_602,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_60,c_58,c_48,c_44,c_42,c_40,c_38,c_36,c_73,c_30,c_417])).

tff(c_662,plain,(
    ! [F_621] :
      ( ~ m1_connsp_2(F_621,'#skF_4','#skF_8')
      | ~ r1_tarski(F_621,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_621,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_62,c_50,c_46,c_112,c_420])).

tff(c_701,plain,(
    ! [A_622] :
      ( ~ m1_connsp_2(A_622,'#skF_4','#skF_8')
      | ~ r1_tarski(A_622,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_193,c_662])).

tff(c_719,plain,(
    ~ m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(resolution,[status(thm)],[c_24,c_701])).

tff(c_26,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_74,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_221,plain,(
    ! [A_574] :
      ( m1_subset_1(A_574,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_574,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_184])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_232,plain,(
    ! [A_575] :
      ( r1_tarski(A_575,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_575,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_221,c_2])).

tff(c_243,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_232])).

tff(c_113,plain,(
    ! [B_553,A_554] :
      ( v2_pre_topc(B_553)
      | ~ m1_pre_topc(B_553,A_554)
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_122,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_113])).

tff(c_131,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_122])).

tff(c_278,plain,(
    ! [B_582,A_583,C_584] :
      ( m1_connsp_2(B_582,A_583,C_584)
      | ~ r2_hidden(C_584,B_582)
      | ~ v3_pre_topc(B_582,A_583)
      | ~ m1_subset_1(C_584,u1_struct_0(A_583))
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0(A_583)))
      | ~ l1_pre_topc(A_583)
      | ~ v2_pre_topc(A_583)
      | v2_struct_0(A_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_280,plain,(
    ! [B_582] :
      ( m1_connsp_2(B_582,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_582)
      | ~ v3_pre_topc(B_582,'#skF_4')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_73,c_278])).

tff(c_285,plain,(
    ! [B_582] :
      ( m1_connsp_2(B_582,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_582)
      | ~ v3_pre_topc(B_582,'#skF_4')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_95,c_280])).

tff(c_729,plain,(
    ! [B_630] :
      ( m1_connsp_2(B_630,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_630)
      | ~ v3_pre_topc(B_630,'#skF_4')
      | ~ m1_subset_1(B_630,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_285])).

tff(c_768,plain,(
    ! [A_631] :
      ( m1_connsp_2(A_631,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',A_631)
      | ~ v3_pre_topc(A_631,'#skF_4')
      | ~ r1_tarski(A_631,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_729])).

tff(c_775,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_243,c_768])).

tff(c_786,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_775])).

tff(c_787,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_719,c_786])).

tff(c_28,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_116,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_113])).

tff(c_125,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_116])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_79])).

tff(c_91,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_282,plain,(
    ! [B_582] :
      ( m1_connsp_2(B_582,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',B_582)
      | ~ v3_pre_topc(B_582,'#skF_3')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_278])).

tff(c_289,plain,(
    ! [B_582] :
      ( m1_connsp_2(B_582,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',B_582)
      | ~ v3_pre_topc(B_582,'#skF_3')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_91,c_282])).

tff(c_323,plain,(
    ! [B_591] :
      ( m1_connsp_2(B_591,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',B_591)
      | ~ v3_pre_topc(B_591,'#skF_3')
      | ~ m1_subset_1(B_591,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_289])).

tff(c_394,plain,(
    ! [A_595] :
      ( m1_connsp_2(A_595,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',A_595)
      | ~ v3_pre_topc(A_595,'#skF_3')
      | ~ r1_tarski(A_595,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_323])).

tff(c_405,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_394])).

tff(c_414,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_405])).

tff(c_422,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_205,plain,(
    ! [D_570,C_571,A_572] :
      ( v3_pre_topc(D_570,C_571)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(u1_struct_0(C_571)))
      | ~ v3_pre_topc(D_570,A_572)
      | ~ m1_pre_topc(C_571,A_572)
      | ~ m1_subset_1(D_570,k1_zfmisc_1(u1_struct_0(A_572)))
      | ~ l1_pre_topc(A_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_590,plain,(
    ! [A_617,C_618,A_619] :
      ( v3_pre_topc(A_617,C_618)
      | ~ v3_pre_topc(A_617,A_619)
      | ~ m1_pre_topc(C_618,A_619)
      | ~ m1_subset_1(A_617,k1_zfmisc_1(u1_struct_0(A_619)))
      | ~ l1_pre_topc(A_619)
      | ~ r1_tarski(A_617,u1_struct_0(C_618)) ) ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_594,plain,(
    ! [A_617] :
      ( v3_pre_topc(A_617,'#skF_3')
      | ~ v3_pre_topc(A_617,'#skF_2')
      | ~ m1_subset_1(A_617,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_617,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_590])).

tff(c_609,plain,(
    ! [A_620] :
      ( v3_pre_topc(A_620,'#skF_3')
      | ~ v3_pre_topc(A_620,'#skF_2')
      | ~ m1_subset_1(A_620,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_620,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_594])).

tff(c_638,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_609])).

tff(c_657,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_638])).

tff(c_659,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_657])).

tff(c_660,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_720,plain,(
    ! [C_623,H_627,E_628,A_626,D_624,F_629,B_625] :
      ( r1_tmap_1(C_623,B_625,k3_tmap_1(A_626,B_625,D_624,C_623,E_628),H_627)
      | ~ r1_tmap_1(D_624,B_625,E_628,H_627)
      | ~ m1_connsp_2(F_629,D_624,H_627)
      | ~ r1_tarski(F_629,u1_struct_0(C_623))
      | ~ m1_subset_1(H_627,u1_struct_0(C_623))
      | ~ m1_subset_1(H_627,u1_struct_0(D_624))
      | ~ m1_subset_1(F_629,k1_zfmisc_1(u1_struct_0(D_624)))
      | ~ m1_pre_topc(C_623,D_624)
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_624),u1_struct_0(B_625))))
      | ~ v1_funct_2(E_628,u1_struct_0(D_624),u1_struct_0(B_625))
      | ~ v1_funct_1(E_628)
      | ~ m1_pre_topc(D_624,A_626)
      | v2_struct_0(D_624)
      | ~ m1_pre_topc(C_623,A_626)
      | v2_struct_0(C_623)
      | ~ l1_pre_topc(B_625)
      | ~ v2_pre_topc(B_625)
      | v2_struct_0(B_625)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_722,plain,(
    ! [C_623,B_625,A_626,E_628] :
      ( r1_tmap_1(C_623,B_625,k3_tmap_1(A_626,B_625,'#skF_3',C_623,E_628),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_625,E_628,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_623))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_623))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_623,'#skF_3')
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_625))))
      | ~ v1_funct_2(E_628,u1_struct_0('#skF_3'),u1_struct_0(B_625))
      | ~ v1_funct_1(E_628)
      | ~ m1_pre_topc('#skF_3',A_626)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_623,A_626)
      | v2_struct_0(C_623)
      | ~ l1_pre_topc(B_625)
      | ~ v2_pre_topc(B_625)
      | v2_struct_0(B_625)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(resolution,[status(thm)],[c_660,c_720])).

tff(c_725,plain,(
    ! [C_623,B_625,A_626,E_628] :
      ( r1_tmap_1(C_623,B_625,k3_tmap_1(A_626,B_625,'#skF_3',C_623,E_628),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_625,E_628,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_623))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_623))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_623,'#skF_3')
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_625))))
      | ~ v1_funct_2(E_628,u1_struct_0('#skF_3'),u1_struct_0(B_625))
      | ~ v1_funct_1(E_628)
      | ~ m1_pre_topc('#skF_3',A_626)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_623,A_626)
      | v2_struct_0(C_623)
      | ~ l1_pre_topc(B_625)
      | ~ v2_pre_topc(B_625)
      | v2_struct_0(B_625)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_722])).

tff(c_726,plain,(
    ! [C_623,B_625,A_626,E_628] :
      ( r1_tmap_1(C_623,B_625,k3_tmap_1(A_626,B_625,'#skF_3',C_623,E_628),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_625,E_628,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_623))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_623))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_623,'#skF_3')
      | ~ m1_subset_1(E_628,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_625))))
      | ~ v1_funct_2(E_628,u1_struct_0('#skF_3'),u1_struct_0(B_625))
      | ~ v1_funct_1(E_628)
      | ~ m1_pre_topc('#skF_3',A_626)
      | ~ m1_pre_topc(C_623,A_626)
      | v2_struct_0(C_623)
      | ~ l1_pre_topc(B_625)
      | ~ v2_pre_topc(B_625)
      | v2_struct_0(B_625)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_725])).

tff(c_925,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_726])).

tff(c_940,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_925])).

tff(c_956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_940])).

tff(c_958,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_726])).

tff(c_10,plain,(
    ! [C_15,A_9,B_13] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(B_13)))
      | ~ m1_pre_topc(B_13,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_974,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_3',A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_958,c_10])).

tff(c_816,plain,(
    ! [A_633,C_634,A_635] :
      ( v3_pre_topc(A_633,C_634)
      | ~ v3_pre_topc(A_633,A_635)
      | ~ m1_pre_topc(C_634,A_635)
      | ~ m1_subset_1(A_633,k1_zfmisc_1(u1_struct_0(A_635)))
      | ~ l1_pre_topc(A_635)
      | ~ r1_tarski(A_633,u1_struct_0(C_634)) ) ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_824,plain,(
    ! [A_633] :
      ( v3_pre_topc(A_633,'#skF_4')
      | ~ v3_pre_topc(A_633,'#skF_2')
      | ~ m1_subset_1(A_633,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_633,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_44,c_816])).

tff(c_1138,plain,(
    ! [A_644] :
      ( v3_pre_topc(A_644,'#skF_4')
      | ~ v3_pre_topc(A_644,'#skF_2')
      | ~ m1_subset_1(A_644,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_644,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_824])).

tff(c_1142,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_974,c_1138])).

tff(c_1174,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_243,c_28,c_1142])).

tff(c_1176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_1174])).

tff(c_1178,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1179,plain,(
    ! [B_645,A_646] :
      ( v2_pre_topc(B_645)
      | ~ m1_pre_topc(B_645,A_646)
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1182,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_1179])).

tff(c_1191,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1182])).

tff(c_1435,plain,(
    ! [B_685,A_686,C_687] :
      ( m1_connsp_2(B_685,A_686,C_687)
      | ~ r2_hidden(C_687,B_685)
      | ~ v3_pre_topc(B_685,A_686)
      | ~ m1_subset_1(C_687,u1_struct_0(A_686))
      | ~ m1_subset_1(B_685,k1_zfmisc_1(u1_struct_0(A_686)))
      | ~ l1_pre_topc(A_686)
      | ~ v2_pre_topc(A_686)
      | v2_struct_0(A_686) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1439,plain,(
    ! [B_685] :
      ( m1_connsp_2(B_685,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',B_685)
      | ~ v3_pre_topc(B_685,'#skF_3')
      | ~ m1_subset_1(B_685,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_1435])).

tff(c_1446,plain,(
    ! [B_685] :
      ( m1_connsp_2(B_685,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',B_685)
      | ~ v3_pre_topc(B_685,'#skF_3')
      | ~ m1_subset_1(B_685,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_91,c_1439])).

tff(c_1487,plain,(
    ! [B_689] :
      ( m1_connsp_2(B_689,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',B_689)
      | ~ v3_pre_topc(B_689,'#skF_3')
      | ~ m1_subset_1(B_689,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1446])).

tff(c_2140,plain,(
    ! [A_742] :
      ( m1_connsp_2(A_742,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',A_742)
      | ~ v3_pre_topc(A_742,'#skF_3')
      | ~ r1_tarski(A_742,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1487])).

tff(c_2151,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_2140])).

tff(c_2160,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_2151])).

tff(c_2161,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2160])).

tff(c_1321,plain,(
    ! [D_671,C_672,A_673] :
      ( v3_pre_topc(D_671,C_672)
      | ~ m1_subset_1(D_671,k1_zfmisc_1(u1_struct_0(C_672)))
      | ~ v3_pre_topc(D_671,A_673)
      | ~ m1_pre_topc(C_672,A_673)
      | ~ m1_subset_1(D_671,k1_zfmisc_1(u1_struct_0(A_673)))
      | ~ l1_pre_topc(A_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2299,plain,(
    ! [A_771,C_772,A_773] :
      ( v3_pre_topc(A_771,C_772)
      | ~ v3_pre_topc(A_771,A_773)
      | ~ m1_pre_topc(C_772,A_773)
      | ~ m1_subset_1(A_771,k1_zfmisc_1(u1_struct_0(A_773)))
      | ~ l1_pre_topc(A_773)
      | ~ r1_tarski(A_771,u1_struct_0(C_772)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1321])).

tff(c_2303,plain,(
    ! [A_771] :
      ( v3_pre_topc(A_771,'#skF_3')
      | ~ v3_pre_topc(A_771,'#skF_2')
      | ~ m1_subset_1(A_771,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_771,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_2299])).

tff(c_2318,plain,(
    ! [A_774] :
      ( v3_pre_topc(A_774,'#skF_3')
      | ~ v3_pre_topc(A_774,'#skF_2')
      | ~ m1_subset_1(A_774,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_774,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2303])).

tff(c_2347,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_2318])).

tff(c_2366,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_2347])).

tff(c_2368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2161,c_2366])).

tff(c_2369,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2160])).

tff(c_2500,plain,(
    ! [F_802,H_800,E_801,B_798,D_797,C_796,A_799] :
      ( r1_tmap_1(C_796,B_798,k3_tmap_1(A_799,B_798,D_797,C_796,E_801),H_800)
      | ~ r1_tmap_1(D_797,B_798,E_801,H_800)
      | ~ m1_connsp_2(F_802,D_797,H_800)
      | ~ r1_tarski(F_802,u1_struct_0(C_796))
      | ~ m1_subset_1(H_800,u1_struct_0(C_796))
      | ~ m1_subset_1(H_800,u1_struct_0(D_797))
      | ~ m1_subset_1(F_802,k1_zfmisc_1(u1_struct_0(D_797)))
      | ~ m1_pre_topc(C_796,D_797)
      | ~ m1_subset_1(E_801,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_797),u1_struct_0(B_798))))
      | ~ v1_funct_2(E_801,u1_struct_0(D_797),u1_struct_0(B_798))
      | ~ v1_funct_1(E_801)
      | ~ m1_pre_topc(D_797,A_799)
      | v2_struct_0(D_797)
      | ~ m1_pre_topc(C_796,A_799)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2502,plain,(
    ! [C_796,B_798,A_799,E_801] :
      ( r1_tmap_1(C_796,B_798,k3_tmap_1(A_799,B_798,'#skF_3',C_796,E_801),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_798,E_801,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_796,'#skF_3')
      | ~ m1_subset_1(E_801,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_798))))
      | ~ v1_funct_2(E_801,u1_struct_0('#skF_3'),u1_struct_0(B_798))
      | ~ v1_funct_1(E_801)
      | ~ m1_pre_topc('#skF_3',A_799)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_796,A_799)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(resolution,[status(thm)],[c_2369,c_2500])).

tff(c_2507,plain,(
    ! [C_796,B_798,A_799,E_801] :
      ( r1_tmap_1(C_796,B_798,k3_tmap_1(A_799,B_798,'#skF_3',C_796,E_801),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_798,E_801,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_796,'#skF_3')
      | ~ m1_subset_1(E_801,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_798))))
      | ~ v1_funct_2(E_801,u1_struct_0('#skF_3'),u1_struct_0(B_798))
      | ~ v1_funct_1(E_801)
      | ~ m1_pre_topc('#skF_3',A_799)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_796,A_799)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2502])).

tff(c_2508,plain,(
    ! [C_796,B_798,A_799,E_801] :
      ( r1_tmap_1(C_796,B_798,k3_tmap_1(A_799,B_798,'#skF_3',C_796,E_801),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_798,E_801,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_796,'#skF_3')
      | ~ m1_subset_1(E_801,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_798))))
      | ~ v1_funct_2(E_801,u1_struct_0('#skF_3'),u1_struct_0(B_798))
      | ~ v1_funct_1(E_801)
      | ~ m1_pre_topc('#skF_3',A_799)
      | ~ m1_pre_topc(C_796,A_799)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2507])).

tff(c_2601,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2508])).

tff(c_2616,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_2601])).

tff(c_2632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2616])).

tff(c_2634,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2508])).

tff(c_2650,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_3',A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_2634,c_10])).

tff(c_1226,plain,(
    ! [C_653,A_654,B_655] :
      ( m1_subset_1(C_653,k1_zfmisc_1(u1_struct_0(A_654)))
      | ~ m1_subset_1(C_653,k1_zfmisc_1(u1_struct_0(B_655)))
      | ~ m1_pre_topc(B_655,A_654)
      | ~ l1_pre_topc(A_654) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1243,plain,(
    ! [A_658,A_659,B_660] :
      ( m1_subset_1(A_658,k1_zfmisc_1(u1_struct_0(A_659)))
      | ~ m1_pre_topc(B_660,A_659)
      | ~ l1_pre_topc(A_659)
      | ~ r1_tarski(A_658,u1_struct_0(B_660)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1226])).

tff(c_1249,plain,(
    ! [A_658] :
      ( m1_subset_1(A_658,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_658,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_36,c_1243])).

tff(c_1282,plain,(
    ! [A_665] :
      ( m1_subset_1(A_665,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_665,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_1249])).

tff(c_1290,plain,(
    ! [A_666] :
      ( r1_tarski(A_666,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_666,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1282,c_2])).

tff(c_1301,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_1290])).

tff(c_1188,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1179])).

tff(c_1197,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1188])).

tff(c_1437,plain,(
    ! [B_685] :
      ( m1_connsp_2(B_685,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_685)
      | ~ v3_pre_topc(B_685,'#skF_4')
      | ~ m1_subset_1(B_685,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_73,c_1435])).

tff(c_1442,plain,(
    ! [B_685] :
      ( m1_connsp_2(B_685,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_685)
      | ~ v3_pre_topc(B_685,'#skF_4')
      | ~ m1_subset_1(B_685,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_95,c_1437])).

tff(c_1448,plain,(
    ! [B_688] :
      ( m1_connsp_2(B_688,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',B_688)
      | ~ v3_pre_topc(B_688,'#skF_4')
      | ~ m1_subset_1(B_688,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1442])).

tff(c_1521,plain,(
    ! [A_690] :
      ( m1_connsp_2(A_690,'#skF_4','#skF_8')
      | ~ r2_hidden('#skF_8',A_690)
      | ~ v3_pre_topc(A_690,'#skF_4')
      | ~ r1_tarski(A_690,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1448])).

tff(c_1528,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1301,c_1521])).

tff(c_1538,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1528])).

tff(c_1542,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1538])).

tff(c_1543,plain,(
    ! [A_691] :
      ( m1_connsp_2(A_691,'#skF_3','#skF_8')
      | ~ r2_hidden('#skF_8',A_691)
      | ~ v3_pre_topc(A_691,'#skF_3')
      | ~ r1_tarski(A_691,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1487])).

tff(c_1554,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_1543])).

tff(c_1563,plain,
    ( m1_connsp_2('#skF_6','#skF_3','#skF_8')
    | ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1554])).

tff(c_1565,plain,(
    ~ v3_pre_topc('#skF_6','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1563])).

tff(c_1697,plain,(
    ! [A_720,C_721,A_722] :
      ( v3_pre_topc(A_720,C_721)
      | ~ v3_pre_topc(A_720,A_722)
      | ~ m1_pre_topc(C_721,A_722)
      | ~ m1_subset_1(A_720,k1_zfmisc_1(u1_struct_0(A_722)))
      | ~ l1_pre_topc(A_722)
      | ~ r1_tarski(A_720,u1_struct_0(C_721)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1321])).

tff(c_1701,plain,(
    ! [A_720] :
      ( v3_pre_topc(A_720,'#skF_3')
      | ~ v3_pre_topc(A_720,'#skF_2')
      | ~ m1_subset_1(A_720,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_720,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1697])).

tff(c_1716,plain,(
    ! [A_723] :
      ( v3_pre_topc(A_723,'#skF_3')
      | ~ v3_pre_topc(A_723,'#skF_2')
      | ~ m1_subset_1(A_723,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_723,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1701])).

tff(c_1745,plain,
    ( v3_pre_topc('#skF_6','#skF_3')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_1716])).

tff(c_1764,plain,(
    v3_pre_topc('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_1745])).

tff(c_1766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1565,c_1764])).

tff(c_1767,plain,(
    m1_connsp_2('#skF_6','#skF_3','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1563])).

tff(c_20,plain,(
    ! [E_285,F_293,H_299,A_45,C_237,D_269,B_173] :
      ( r1_tmap_1(C_237,B_173,k3_tmap_1(A_45,B_173,D_269,C_237,E_285),H_299)
      | ~ r1_tmap_1(D_269,B_173,E_285,H_299)
      | ~ m1_connsp_2(F_293,D_269,H_299)
      | ~ r1_tarski(F_293,u1_struct_0(C_237))
      | ~ m1_subset_1(H_299,u1_struct_0(C_237))
      | ~ m1_subset_1(H_299,u1_struct_0(D_269))
      | ~ m1_subset_1(F_293,k1_zfmisc_1(u1_struct_0(D_269)))
      | ~ m1_pre_topc(C_237,D_269)
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_269),u1_struct_0(B_173))))
      | ~ v1_funct_2(E_285,u1_struct_0(D_269),u1_struct_0(B_173))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc(D_269,A_45)
      | v2_struct_0(D_269)
      | ~ m1_pre_topc(C_237,A_45)
      | v2_struct_0(C_237)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1771,plain,(
    ! [C_237,B_173,A_45,E_285] :
      ( r1_tmap_1(C_237,B_173,k3_tmap_1(A_45,B_173,'#skF_3',C_237,E_285),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_173,E_285,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_237))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_237))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_237,'#skF_3')
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_173))))
      | ~ v1_funct_2(E_285,u1_struct_0('#skF_3'),u1_struct_0(B_173))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc('#skF_3',A_45)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_237,A_45)
      | v2_struct_0(C_237)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_1767,c_20])).

tff(c_1774,plain,(
    ! [C_237,B_173,A_45,E_285] :
      ( r1_tmap_1(C_237,B_173,k3_tmap_1(A_45,B_173,'#skF_3',C_237,E_285),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_173,E_285,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_237))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_237))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_237,'#skF_3')
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_173))))
      | ~ v1_funct_2(E_285,u1_struct_0('#skF_3'),u1_struct_0(B_173))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc('#skF_3',A_45)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_237,A_45)
      | v2_struct_0(C_237)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1771])).

tff(c_1775,plain,(
    ! [C_237,B_173,A_45,E_285] :
      ( r1_tmap_1(C_237,B_173,k3_tmap_1(A_45,B_173,'#skF_3',C_237,E_285),'#skF_8')
      | ~ r1_tmap_1('#skF_3',B_173,E_285,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_237))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_237))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_pre_topc(C_237,'#skF_3')
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_173))))
      | ~ v1_funct_2(E_285,u1_struct_0('#skF_3'),u1_struct_0(B_173))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc('#skF_3',A_45)
      | ~ m1_pre_topc(C_237,A_45)
      | v2_struct_0(C_237)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1774])).

tff(c_1799,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1775])).

tff(c_1814,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_1799])).

tff(c_1830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1814])).

tff(c_1832,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_1848,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ m1_pre_topc('#skF_3',A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_1832,c_10])).

tff(c_1923,plain,(
    ! [A_734,C_735,A_736] :
      ( v3_pre_topc(A_734,C_735)
      | ~ v3_pre_topc(A_734,A_736)
      | ~ m1_pre_topc(C_735,A_736)
      | ~ m1_subset_1(A_734,k1_zfmisc_1(u1_struct_0(A_736)))
      | ~ l1_pre_topc(A_736)
      | ~ r1_tarski(A_734,u1_struct_0(C_735)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1321])).

tff(c_1931,plain,(
    ! [A_734] :
      ( v3_pre_topc(A_734,'#skF_4')
      | ~ v3_pre_topc(A_734,'#skF_2')
      | ~ m1_subset_1(A_734,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_734,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_44,c_1923])).

tff(c_2097,plain,(
    ! [A_741] :
      ( v3_pre_topc(A_741,'#skF_4')
      | ~ v3_pre_topc(A_741,'#skF_2')
      | ~ m1_subset_1(A_741,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_741,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1931])).

tff(c_2101,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1848,c_2097])).

tff(c_2133,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1301,c_28,c_2101])).

tff(c_2135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1542,c_2133])).

tff(c_2136,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1538])).

tff(c_2504,plain,(
    ! [C_796,B_798,A_799,E_801] :
      ( r1_tmap_1(C_796,B_798,k3_tmap_1(A_799,B_798,'#skF_4',C_796,E_801),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_798,E_801,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(C_796,'#skF_4')
      | ~ m1_subset_1(E_801,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_798))))
      | ~ v1_funct_2(E_801,u1_struct_0('#skF_4'),u1_struct_0(B_798))
      | ~ v1_funct_1(E_801)
      | ~ m1_pre_topc('#skF_4',A_799)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_796,A_799)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(resolution,[status(thm)],[c_2136,c_2500])).

tff(c_2511,plain,(
    ! [C_796,B_798,A_799,E_801] :
      ( r1_tmap_1(C_796,B_798,k3_tmap_1(A_799,B_798,'#skF_4',C_796,E_801),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_798,E_801,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(C_796,'#skF_4')
      | ~ m1_subset_1(E_801,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_798))))
      | ~ v1_funct_2(E_801,u1_struct_0('#skF_4'),u1_struct_0(B_798))
      | ~ v1_funct_1(E_801)
      | ~ m1_pre_topc('#skF_4',A_799)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_796,A_799)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_2504])).

tff(c_2512,plain,(
    ! [C_796,B_798,A_799,E_801] :
      ( r1_tmap_1(C_796,B_798,k3_tmap_1(A_799,B_798,'#skF_4',C_796,E_801),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_798,E_801,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_796))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(C_796,'#skF_4')
      | ~ m1_subset_1(E_801,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_798))))
      | ~ v1_funct_2(E_801,u1_struct_0('#skF_4'),u1_struct_0(B_798))
      | ~ v1_funct_1(E_801)
      | ~ m1_pre_topc('#skF_4',A_799)
      | ~ m1_pre_topc(C_796,A_799)
      | v2_struct_0(C_796)
      | ~ l1_pre_topc(B_798)
      | ~ v2_pre_topc(B_798)
      | v2_struct_0(B_798)
      | ~ l1_pre_topc(A_799)
      | ~ v2_pre_topc(A_799)
      | v2_struct_0(A_799) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2511])).

tff(c_2815,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_2512])).

tff(c_2818,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2650,c_2815])).

tff(c_2840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_36,c_2818])).

tff(c_3399,plain,(
    ! [C_840,B_841,A_842,E_843] :
      ( r1_tmap_1(C_840,B_841,k3_tmap_1(A_842,B_841,'#skF_4',C_840,E_843),'#skF_8')
      | ~ r1_tmap_1('#skF_4',B_841,E_843,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_840))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_840))
      | ~ m1_pre_topc(C_840,'#skF_4')
      | ~ m1_subset_1(E_843,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_841))))
      | ~ v1_funct_2(E_843,u1_struct_0('#skF_4'),u1_struct_0(B_841))
      | ~ v1_funct_1(E_843)
      | ~ m1_pre_topc('#skF_4',A_842)
      | ~ m1_pre_topc(C_840,A_842)
      | v2_struct_0(C_840)
      | ~ l1_pre_topc(B_841)
      | ~ v2_pre_topc(B_841)
      | v2_struct_0(B_841)
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | v2_struct_0(A_842) ) ),
    inference(splitRight,[status(thm)],[c_2512])).

tff(c_3401,plain,(
    ! [C_840,A_842] :
      ( r1_tmap_1(C_840,'#skF_1',k3_tmap_1(A_842,'#skF_1','#skF_4',C_840,'#skF_5'),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_840))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_840))
      | ~ m1_pre_topc(C_840,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_842)
      | ~ m1_pre_topc(C_840,A_842)
      | v2_struct_0(C_840)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | v2_struct_0(A_842) ) ),
    inference(resolution,[status(thm)],[c_38,c_3399])).

tff(c_3407,plain,(
    ! [C_840,A_842] :
      ( r1_tmap_1(C_840,'#skF_1',k3_tmap_1(A_842,'#skF_1','#skF_4',C_840,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_840))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_840))
      | ~ m1_pre_topc(C_840,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_842)
      | ~ m1_pre_topc(C_840,A_842)
      | v2_struct_0(C_840)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_842)
      | ~ v2_pre_topc(A_842)
      | v2_struct_0(A_842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_42,c_40,c_1178,c_3401])).

tff(c_3452,plain,(
    ! [C_848,A_849] :
      ( r1_tmap_1(C_848,'#skF_1',k3_tmap_1(A_849,'#skF_1','#skF_4',C_848,'#skF_5'),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(C_848))
      | ~ m1_subset_1('#skF_8',u1_struct_0(C_848))
      | ~ m1_pre_topc(C_848,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_849)
      | ~ m1_pre_topc(C_848,A_849)
      | v2_struct_0(C_848)
      | ~ l1_pre_topc(A_849)
      | ~ v2_pre_topc(A_849)
      | v2_struct_0(A_849) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_3407])).

tff(c_1177,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3457,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3452,c_1177])).

tff(c_3464,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_44,c_36,c_30,c_24,c_3457])).

tff(c_3466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_50,c_3464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n010.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 14:17:29 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/1.97  
% 5.34/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.34/1.97  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 5.34/1.97  
% 5.34/1.97  %Foreground sorts:
% 5.34/1.97  
% 5.34/1.97  
% 5.34/1.97  %Background operators:
% 5.34/1.97  
% 5.34/1.97  
% 5.34/1.97  %Foreground operators:
% 5.34/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.34/1.97  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.34/1.97  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.34/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.34/1.97  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.34/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.34/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.34/1.97  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.34/1.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.34/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.34/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.34/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.34/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.34/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.34/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.34/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.34/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.34/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.34/1.97  tff('#skF_8', type, '#skF_8': $i).
% 5.34/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.34/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.34/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.34/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.34/1.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.34/1.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.34/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.34/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.34/1.97  
% 5.73/2.01  tff(f_216, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 5.73/2.01  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.73/2.01  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.73/2.01  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 5.73/2.01  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 5.73/2.01  tff(f_38, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.73/2.01  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.73/2.01  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 5.73/2.01  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_30, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_24, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_62, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_60, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_58, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_40, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_79, plain, (![B_547, A_548]: (l1_pre_topc(B_547) | ~m1_pre_topc(B_547, A_548) | ~l1_pre_topc(A_548))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.73/2.01  tff(c_88, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_79])).
% 5.73/2.01  tff(c_95, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_88])).
% 5.73/2.01  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.73/2.01  tff(c_161, plain, (![C_561, A_562, B_563]: (m1_subset_1(C_561, k1_zfmisc_1(u1_struct_0(A_562))) | ~m1_subset_1(C_561, k1_zfmisc_1(u1_struct_0(B_563))) | ~m1_pre_topc(B_563, A_562) | ~l1_pre_topc(A_562))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.73/2.01  tff(c_178, plain, (![A_566, A_567, B_568]: (m1_subset_1(A_566, k1_zfmisc_1(u1_struct_0(A_567))) | ~m1_pre_topc(B_568, A_567) | ~l1_pre_topc(A_567) | ~r1_tarski(A_566, u1_struct_0(B_568)))), inference(resolution, [status(thm)], [c_4, c_161])).
% 5.73/2.01  tff(c_184, plain, (![A_566]: (m1_subset_1(A_566, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_566, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_178])).
% 5.73/2.01  tff(c_193, plain, (![A_566]: (m1_subset_1(A_566, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_566, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_184])).
% 5.73/2.01  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_22, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_64, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_72, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_64])).
% 5.73/2.01  tff(c_112, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_72])).
% 5.73/2.01  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_32, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_73, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_32])).
% 5.73/2.01  tff(c_70, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_71, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_70])).
% 5.73/2.01  tff(c_160, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_112, c_71])).
% 5.73/2.01  tff(c_415, plain, (![E_601, A_599, B_598, D_597, C_596, H_600, F_602]: (r1_tmap_1(D_597, B_598, E_601, H_600) | ~r1_tmap_1(C_596, B_598, k3_tmap_1(A_599, B_598, D_597, C_596, E_601), H_600) | ~m1_connsp_2(F_602, D_597, H_600) | ~r1_tarski(F_602, u1_struct_0(C_596)) | ~m1_subset_1(H_600, u1_struct_0(C_596)) | ~m1_subset_1(H_600, u1_struct_0(D_597)) | ~m1_subset_1(F_602, k1_zfmisc_1(u1_struct_0(D_597))) | ~m1_pre_topc(C_596, D_597) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_597), u1_struct_0(B_598)))) | ~v1_funct_2(E_601, u1_struct_0(D_597), u1_struct_0(B_598)) | ~v1_funct_1(E_601) | ~m1_pre_topc(D_597, A_599) | v2_struct_0(D_597) | ~m1_pre_topc(C_596, A_599) | v2_struct_0(C_596) | ~l1_pre_topc(B_598) | ~v2_pre_topc(B_598) | v2_struct_0(B_598) | ~l1_pre_topc(A_599) | ~v2_pre_topc(A_599) | v2_struct_0(A_599))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.73/2.01  tff(c_417, plain, (![F_602]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_connsp_2(F_602, '#skF_4', '#skF_8') | ~r1_tarski(F_602, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_602, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_160, c_415])).
% 5.73/2.01  tff(c_420, plain, (![F_602]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_connsp_2(F_602, '#skF_4', '#skF_8') | ~r1_tarski(F_602, u1_struct_0('#skF_3')) | ~m1_subset_1(F_602, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_60, c_58, c_48, c_44, c_42, c_40, c_38, c_36, c_73, c_30, c_417])).
% 5.73/2.01  tff(c_662, plain, (![F_621]: (~m1_connsp_2(F_621, '#skF_4', '#skF_8') | ~r1_tarski(F_621, u1_struct_0('#skF_3')) | ~m1_subset_1(F_621, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_62, c_50, c_46, c_112, c_420])).
% 5.73/2.01  tff(c_701, plain, (![A_622]: (~m1_connsp_2(A_622, '#skF_4', '#skF_8') | ~r1_tarski(A_622, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_193, c_662])).
% 5.73/2.01  tff(c_719, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(resolution, [status(thm)], [c_24, c_701])).
% 5.73/2.01  tff(c_26, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_74, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 5.73/2.01  tff(c_221, plain, (![A_574]: (m1_subset_1(A_574, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_574, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_184])).
% 5.73/2.01  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.73/2.01  tff(c_232, plain, (![A_575]: (r1_tarski(A_575, u1_struct_0('#skF_4')) | ~r1_tarski(A_575, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_221, c_2])).
% 5.73/2.01  tff(c_243, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_232])).
% 5.73/2.01  tff(c_113, plain, (![B_553, A_554]: (v2_pre_topc(B_553) | ~m1_pre_topc(B_553, A_554) | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.73/2.01  tff(c_122, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_113])).
% 5.73/2.01  tff(c_131, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_122])).
% 5.73/2.01  tff(c_278, plain, (![B_582, A_583, C_584]: (m1_connsp_2(B_582, A_583, C_584) | ~r2_hidden(C_584, B_582) | ~v3_pre_topc(B_582, A_583) | ~m1_subset_1(C_584, u1_struct_0(A_583)) | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0(A_583))) | ~l1_pre_topc(A_583) | ~v2_pre_topc(A_583) | v2_struct_0(A_583))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.73/2.01  tff(c_280, plain, (![B_582]: (m1_connsp_2(B_582, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_582) | ~v3_pre_topc(B_582, '#skF_4') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_73, c_278])).
% 5.73/2.01  tff(c_285, plain, (![B_582]: (m1_connsp_2(B_582, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_582) | ~v3_pre_topc(B_582, '#skF_4') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_95, c_280])).
% 5.73/2.01  tff(c_729, plain, (![B_630]: (m1_connsp_2(B_630, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_630) | ~v3_pre_topc(B_630, '#skF_4') | ~m1_subset_1(B_630, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_285])).
% 5.73/2.01  tff(c_768, plain, (![A_631]: (m1_connsp_2(A_631, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', A_631) | ~v3_pre_topc(A_631, '#skF_4') | ~r1_tarski(A_631, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_729])).
% 5.73/2.01  tff(c_775, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_243, c_768])).
% 5.73/2.01  tff(c_786, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_775])).
% 5.73/2.01  tff(c_787, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_719, c_786])).
% 5.73/2.01  tff(c_28, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_116, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_113])).
% 5.73/2.01  tff(c_125, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_116])).
% 5.73/2.01  tff(c_82, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_79])).
% 5.73/2.01  tff(c_91, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 5.73/2.01  tff(c_282, plain, (![B_582]: (m1_connsp_2(B_582, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', B_582) | ~v3_pre_topc(B_582, '#skF_3') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_278])).
% 5.73/2.01  tff(c_289, plain, (![B_582]: (m1_connsp_2(B_582, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', B_582) | ~v3_pre_topc(B_582, '#skF_3') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_91, c_282])).
% 5.73/2.01  tff(c_323, plain, (![B_591]: (m1_connsp_2(B_591, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', B_591) | ~v3_pre_topc(B_591, '#skF_3') | ~m1_subset_1(B_591, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_289])).
% 5.73/2.01  tff(c_394, plain, (![A_595]: (m1_connsp_2(A_595, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', A_595) | ~v3_pre_topc(A_595, '#skF_3') | ~r1_tarski(A_595, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4, c_323])).
% 5.73/2.01  tff(c_405, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_394])).
% 5.73/2.01  tff(c_414, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_405])).
% 5.73/2.01  tff(c_422, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_414])).
% 5.73/2.01  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_216])).
% 5.73/2.01  tff(c_205, plain, (![D_570, C_571, A_572]: (v3_pre_topc(D_570, C_571) | ~m1_subset_1(D_570, k1_zfmisc_1(u1_struct_0(C_571))) | ~v3_pre_topc(D_570, A_572) | ~m1_pre_topc(C_571, A_572) | ~m1_subset_1(D_570, k1_zfmisc_1(u1_struct_0(A_572))) | ~l1_pre_topc(A_572))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.73/2.01  tff(c_590, plain, (![A_617, C_618, A_619]: (v3_pre_topc(A_617, C_618) | ~v3_pre_topc(A_617, A_619) | ~m1_pre_topc(C_618, A_619) | ~m1_subset_1(A_617, k1_zfmisc_1(u1_struct_0(A_619))) | ~l1_pre_topc(A_619) | ~r1_tarski(A_617, u1_struct_0(C_618)))), inference(resolution, [status(thm)], [c_4, c_205])).
% 5.73/2.01  tff(c_594, plain, (![A_617]: (v3_pre_topc(A_617, '#skF_3') | ~v3_pre_topc(A_617, '#skF_2') | ~m1_subset_1(A_617, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_617, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_590])).
% 5.73/2.01  tff(c_609, plain, (![A_620]: (v3_pre_topc(A_620, '#skF_3') | ~v3_pre_topc(A_620, '#skF_2') | ~m1_subset_1(A_620, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_620, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_594])).
% 5.73/2.01  tff(c_638, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_609])).
% 5.73/2.01  tff(c_657, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_638])).
% 5.73/2.01  tff(c_659, plain, $false, inference(negUnitSimplification, [status(thm)], [c_422, c_657])).
% 5.73/2.01  tff(c_660, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_414])).
% 5.73/2.01  tff(c_720, plain, (![C_623, H_627, E_628, A_626, D_624, F_629, B_625]: (r1_tmap_1(C_623, B_625, k3_tmap_1(A_626, B_625, D_624, C_623, E_628), H_627) | ~r1_tmap_1(D_624, B_625, E_628, H_627) | ~m1_connsp_2(F_629, D_624, H_627) | ~r1_tarski(F_629, u1_struct_0(C_623)) | ~m1_subset_1(H_627, u1_struct_0(C_623)) | ~m1_subset_1(H_627, u1_struct_0(D_624)) | ~m1_subset_1(F_629, k1_zfmisc_1(u1_struct_0(D_624))) | ~m1_pre_topc(C_623, D_624) | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_624), u1_struct_0(B_625)))) | ~v1_funct_2(E_628, u1_struct_0(D_624), u1_struct_0(B_625)) | ~v1_funct_1(E_628) | ~m1_pre_topc(D_624, A_626) | v2_struct_0(D_624) | ~m1_pre_topc(C_623, A_626) | v2_struct_0(C_623) | ~l1_pre_topc(B_625) | ~v2_pre_topc(B_625) | v2_struct_0(B_625) | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.73/2.01  tff(c_722, plain, (![C_623, B_625, A_626, E_628]: (r1_tmap_1(C_623, B_625, k3_tmap_1(A_626, B_625, '#skF_3', C_623, E_628), '#skF_8') | ~r1_tmap_1('#skF_3', B_625, E_628, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_623)) | ~m1_subset_1('#skF_8', u1_struct_0(C_623)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_623, '#skF_3') | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_625)))) | ~v1_funct_2(E_628, u1_struct_0('#skF_3'), u1_struct_0(B_625)) | ~v1_funct_1(E_628) | ~m1_pre_topc('#skF_3', A_626) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_623, A_626) | v2_struct_0(C_623) | ~l1_pre_topc(B_625) | ~v2_pre_topc(B_625) | v2_struct_0(B_625) | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(resolution, [status(thm)], [c_660, c_720])).
% 5.73/2.01  tff(c_725, plain, (![C_623, B_625, A_626, E_628]: (r1_tmap_1(C_623, B_625, k3_tmap_1(A_626, B_625, '#skF_3', C_623, E_628), '#skF_8') | ~r1_tmap_1('#skF_3', B_625, E_628, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_623)) | ~m1_subset_1('#skF_8', u1_struct_0(C_623)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_623, '#skF_3') | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_625)))) | ~v1_funct_2(E_628, u1_struct_0('#skF_3'), u1_struct_0(B_625)) | ~v1_funct_1(E_628) | ~m1_pre_topc('#skF_3', A_626) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_623, A_626) | v2_struct_0(C_623) | ~l1_pre_topc(B_625) | ~v2_pre_topc(B_625) | v2_struct_0(B_625) | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_722])).
% 5.73/2.01  tff(c_726, plain, (![C_623, B_625, A_626, E_628]: (r1_tmap_1(C_623, B_625, k3_tmap_1(A_626, B_625, '#skF_3', C_623, E_628), '#skF_8') | ~r1_tmap_1('#skF_3', B_625, E_628, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_623)) | ~m1_subset_1('#skF_8', u1_struct_0(C_623)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_623, '#skF_3') | ~m1_subset_1(E_628, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_625)))) | ~v1_funct_2(E_628, u1_struct_0('#skF_3'), u1_struct_0(B_625)) | ~v1_funct_1(E_628) | ~m1_pre_topc('#skF_3', A_626) | ~m1_pre_topc(C_623, A_626) | v2_struct_0(C_623) | ~l1_pre_topc(B_625) | ~v2_pre_topc(B_625) | v2_struct_0(B_625) | ~l1_pre_topc(A_626) | ~v2_pre_topc(A_626) | v2_struct_0(A_626))), inference(negUnitSimplification, [status(thm)], [c_50, c_725])).
% 5.73/2.01  tff(c_925, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_726])).
% 5.73/2.01  tff(c_940, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_925])).
% 5.73/2.01  tff(c_956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_940])).
% 5.73/2.01  tff(c_958, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_726])).
% 5.73/2.01  tff(c_10, plain, (![C_15, A_9, B_13]: (m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_subset_1(C_15, k1_zfmisc_1(u1_struct_0(B_13))) | ~m1_pre_topc(B_13, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.73/2.01  tff(c_974, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_3', A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_958, c_10])).
% 5.73/2.01  tff(c_816, plain, (![A_633, C_634, A_635]: (v3_pre_topc(A_633, C_634) | ~v3_pre_topc(A_633, A_635) | ~m1_pre_topc(C_634, A_635) | ~m1_subset_1(A_633, k1_zfmisc_1(u1_struct_0(A_635))) | ~l1_pre_topc(A_635) | ~r1_tarski(A_633, u1_struct_0(C_634)))), inference(resolution, [status(thm)], [c_4, c_205])).
% 5.73/2.01  tff(c_824, plain, (![A_633]: (v3_pre_topc(A_633, '#skF_4') | ~v3_pre_topc(A_633, '#skF_2') | ~m1_subset_1(A_633, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_633, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_44, c_816])).
% 5.73/2.01  tff(c_1138, plain, (![A_644]: (v3_pre_topc(A_644, '#skF_4') | ~v3_pre_topc(A_644, '#skF_2') | ~m1_subset_1(A_644, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_644, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_824])).
% 5.73/2.01  tff(c_1142, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_974, c_1138])).
% 5.73/2.01  tff(c_1174, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_243, c_28, c_1142])).
% 5.73/2.01  tff(c_1176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_787, c_1174])).
% 5.73/2.01  tff(c_1178, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 5.73/2.01  tff(c_1179, plain, (![B_645, A_646]: (v2_pre_topc(B_645) | ~m1_pre_topc(B_645, A_646) | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.73/2.01  tff(c_1182, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_1179])).
% 5.73/2.01  tff(c_1191, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1182])).
% 5.73/2.01  tff(c_1435, plain, (![B_685, A_686, C_687]: (m1_connsp_2(B_685, A_686, C_687) | ~r2_hidden(C_687, B_685) | ~v3_pre_topc(B_685, A_686) | ~m1_subset_1(C_687, u1_struct_0(A_686)) | ~m1_subset_1(B_685, k1_zfmisc_1(u1_struct_0(A_686))) | ~l1_pre_topc(A_686) | ~v2_pre_topc(A_686) | v2_struct_0(A_686))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.73/2.01  tff(c_1439, plain, (![B_685]: (m1_connsp_2(B_685, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', B_685) | ~v3_pre_topc(B_685, '#skF_3') | ~m1_subset_1(B_685, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_1435])).
% 5.73/2.01  tff(c_1446, plain, (![B_685]: (m1_connsp_2(B_685, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', B_685) | ~v3_pre_topc(B_685, '#skF_3') | ~m1_subset_1(B_685, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_91, c_1439])).
% 5.73/2.01  tff(c_1487, plain, (![B_689]: (m1_connsp_2(B_689, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', B_689) | ~v3_pre_topc(B_689, '#skF_3') | ~m1_subset_1(B_689, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_1446])).
% 5.73/2.01  tff(c_2140, plain, (![A_742]: (m1_connsp_2(A_742, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', A_742) | ~v3_pre_topc(A_742, '#skF_3') | ~r1_tarski(A_742, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4, c_1487])).
% 5.73/2.01  tff(c_2151, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_2140])).
% 5.73/2.01  tff(c_2160, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_2151])).
% 5.73/2.01  tff(c_2161, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_2160])).
% 5.73/2.01  tff(c_1321, plain, (![D_671, C_672, A_673]: (v3_pre_topc(D_671, C_672) | ~m1_subset_1(D_671, k1_zfmisc_1(u1_struct_0(C_672))) | ~v3_pre_topc(D_671, A_673) | ~m1_pre_topc(C_672, A_673) | ~m1_subset_1(D_671, k1_zfmisc_1(u1_struct_0(A_673))) | ~l1_pre_topc(A_673))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.73/2.01  tff(c_2299, plain, (![A_771, C_772, A_773]: (v3_pre_topc(A_771, C_772) | ~v3_pre_topc(A_771, A_773) | ~m1_pre_topc(C_772, A_773) | ~m1_subset_1(A_771, k1_zfmisc_1(u1_struct_0(A_773))) | ~l1_pre_topc(A_773) | ~r1_tarski(A_771, u1_struct_0(C_772)))), inference(resolution, [status(thm)], [c_4, c_1321])).
% 5.73/2.01  tff(c_2303, plain, (![A_771]: (v3_pre_topc(A_771, '#skF_3') | ~v3_pre_topc(A_771, '#skF_2') | ~m1_subset_1(A_771, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_771, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_2299])).
% 5.73/2.01  tff(c_2318, plain, (![A_774]: (v3_pre_topc(A_774, '#skF_3') | ~v3_pre_topc(A_774, '#skF_2') | ~m1_subset_1(A_774, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_774, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2303])).
% 5.73/2.01  tff(c_2347, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_2318])).
% 5.73/2.01  tff(c_2366, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_2347])).
% 5.73/2.01  tff(c_2368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2161, c_2366])).
% 5.73/2.01  tff(c_2369, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_2160])).
% 5.73/2.01  tff(c_2500, plain, (![F_802, H_800, E_801, B_798, D_797, C_796, A_799]: (r1_tmap_1(C_796, B_798, k3_tmap_1(A_799, B_798, D_797, C_796, E_801), H_800) | ~r1_tmap_1(D_797, B_798, E_801, H_800) | ~m1_connsp_2(F_802, D_797, H_800) | ~r1_tarski(F_802, u1_struct_0(C_796)) | ~m1_subset_1(H_800, u1_struct_0(C_796)) | ~m1_subset_1(H_800, u1_struct_0(D_797)) | ~m1_subset_1(F_802, k1_zfmisc_1(u1_struct_0(D_797))) | ~m1_pre_topc(C_796, D_797) | ~m1_subset_1(E_801, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_797), u1_struct_0(B_798)))) | ~v1_funct_2(E_801, u1_struct_0(D_797), u1_struct_0(B_798)) | ~v1_funct_1(E_801) | ~m1_pre_topc(D_797, A_799) | v2_struct_0(D_797) | ~m1_pre_topc(C_796, A_799) | v2_struct_0(C_796) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.73/2.01  tff(c_2502, plain, (![C_796, B_798, A_799, E_801]: (r1_tmap_1(C_796, B_798, k3_tmap_1(A_799, B_798, '#skF_3', C_796, E_801), '#skF_8') | ~r1_tmap_1('#skF_3', B_798, E_801, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_796, '#skF_3') | ~m1_subset_1(E_801, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_798)))) | ~v1_funct_2(E_801, u1_struct_0('#skF_3'), u1_struct_0(B_798)) | ~v1_funct_1(E_801) | ~m1_pre_topc('#skF_3', A_799) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_796, A_799) | v2_struct_0(C_796) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(resolution, [status(thm)], [c_2369, c_2500])).
% 5.73/2.01  tff(c_2507, plain, (![C_796, B_798, A_799, E_801]: (r1_tmap_1(C_796, B_798, k3_tmap_1(A_799, B_798, '#skF_3', C_796, E_801), '#skF_8') | ~r1_tmap_1('#skF_3', B_798, E_801, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0(C_796)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_796, '#skF_3') | ~m1_subset_1(E_801, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_798)))) | ~v1_funct_2(E_801, u1_struct_0('#skF_3'), u1_struct_0(B_798)) | ~v1_funct_1(E_801) | ~m1_pre_topc('#skF_3', A_799) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_796, A_799) | v2_struct_0(C_796) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2502])).
% 5.73/2.01  tff(c_2508, plain, (![C_796, B_798, A_799, E_801]: (r1_tmap_1(C_796, B_798, k3_tmap_1(A_799, B_798, '#skF_3', C_796, E_801), '#skF_8') | ~r1_tmap_1('#skF_3', B_798, E_801, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0(C_796)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_796, '#skF_3') | ~m1_subset_1(E_801, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_798)))) | ~v1_funct_2(E_801, u1_struct_0('#skF_3'), u1_struct_0(B_798)) | ~v1_funct_1(E_801) | ~m1_pre_topc('#skF_3', A_799) | ~m1_pre_topc(C_796, A_799) | v2_struct_0(C_796) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(negUnitSimplification, [status(thm)], [c_50, c_2507])).
% 5.73/2.01  tff(c_2601, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_2508])).
% 5.73/2.01  tff(c_2616, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_2601])).
% 5.73/2.01  tff(c_2632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2616])).
% 5.73/2.01  tff(c_2634, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_2508])).
% 5.73/2.01  tff(c_2650, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_3', A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_2634, c_10])).
% 5.73/2.01  tff(c_1226, plain, (![C_653, A_654, B_655]: (m1_subset_1(C_653, k1_zfmisc_1(u1_struct_0(A_654))) | ~m1_subset_1(C_653, k1_zfmisc_1(u1_struct_0(B_655))) | ~m1_pre_topc(B_655, A_654) | ~l1_pre_topc(A_654))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.73/2.01  tff(c_1243, plain, (![A_658, A_659, B_660]: (m1_subset_1(A_658, k1_zfmisc_1(u1_struct_0(A_659))) | ~m1_pre_topc(B_660, A_659) | ~l1_pre_topc(A_659) | ~r1_tarski(A_658, u1_struct_0(B_660)))), inference(resolution, [status(thm)], [c_4, c_1226])).
% 5.73/2.01  tff(c_1249, plain, (![A_658]: (m1_subset_1(A_658, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_658, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_36, c_1243])).
% 5.73/2.01  tff(c_1282, plain, (![A_665]: (m1_subset_1(A_665, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_665, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_1249])).
% 5.73/2.01  tff(c_1290, plain, (![A_666]: (r1_tarski(A_666, u1_struct_0('#skF_4')) | ~r1_tarski(A_666, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1282, c_2])).
% 5.73/2.01  tff(c_1301, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_1290])).
% 5.73/2.01  tff(c_1188, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1179])).
% 5.73/2.01  tff(c_1197, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1188])).
% 5.73/2.01  tff(c_1437, plain, (![B_685]: (m1_connsp_2(B_685, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_685) | ~v3_pre_topc(B_685, '#skF_4') | ~m1_subset_1(B_685, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_73, c_1435])).
% 5.73/2.01  tff(c_1442, plain, (![B_685]: (m1_connsp_2(B_685, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_685) | ~v3_pre_topc(B_685, '#skF_4') | ~m1_subset_1(B_685, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_95, c_1437])).
% 5.73/2.01  tff(c_1448, plain, (![B_688]: (m1_connsp_2(B_688, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', B_688) | ~v3_pre_topc(B_688, '#skF_4') | ~m1_subset_1(B_688, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_46, c_1442])).
% 5.73/2.01  tff(c_1521, plain, (![A_690]: (m1_connsp_2(A_690, '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', A_690) | ~v3_pre_topc(A_690, '#skF_4') | ~r1_tarski(A_690, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_1448])).
% 5.73/2.01  tff(c_1528, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1301, c_1521])).
% 5.73/2.01  tff(c_1538, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1528])).
% 5.73/2.01  tff(c_1542, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1538])).
% 5.73/2.01  tff(c_1543, plain, (![A_691]: (m1_connsp_2(A_691, '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', A_691) | ~v3_pre_topc(A_691, '#skF_3') | ~r1_tarski(A_691, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_4, c_1487])).
% 5.73/2.01  tff(c_1554, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_1543])).
% 5.73/2.01  tff(c_1563, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8') | ~v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1554])).
% 5.73/2.01  tff(c_1565, plain, (~v3_pre_topc('#skF_6', '#skF_3')), inference(splitLeft, [status(thm)], [c_1563])).
% 5.73/2.01  tff(c_1697, plain, (![A_720, C_721, A_722]: (v3_pre_topc(A_720, C_721) | ~v3_pre_topc(A_720, A_722) | ~m1_pre_topc(C_721, A_722) | ~m1_subset_1(A_720, k1_zfmisc_1(u1_struct_0(A_722))) | ~l1_pre_topc(A_722) | ~r1_tarski(A_720, u1_struct_0(C_721)))), inference(resolution, [status(thm)], [c_4, c_1321])).
% 5.73/2.01  tff(c_1701, plain, (![A_720]: (v3_pre_topc(A_720, '#skF_3') | ~v3_pre_topc(A_720, '#skF_2') | ~m1_subset_1(A_720, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_720, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_1697])).
% 5.73/2.01  tff(c_1716, plain, (![A_723]: (v3_pre_topc(A_723, '#skF_3') | ~v3_pre_topc(A_723, '#skF_2') | ~m1_subset_1(A_723, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_723, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1701])).
% 5.73/2.01  tff(c_1745, plain, (v3_pre_topc('#skF_6', '#skF_3') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_1716])).
% 5.73/2.01  tff(c_1764, plain, (v3_pre_topc('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_1745])).
% 5.73/2.01  tff(c_1766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1565, c_1764])).
% 5.73/2.01  tff(c_1767, plain, (m1_connsp_2('#skF_6', '#skF_3', '#skF_8')), inference(splitRight, [status(thm)], [c_1563])).
% 5.73/2.01  tff(c_20, plain, (![E_285, F_293, H_299, A_45, C_237, D_269, B_173]: (r1_tmap_1(C_237, B_173, k3_tmap_1(A_45, B_173, D_269, C_237, E_285), H_299) | ~r1_tmap_1(D_269, B_173, E_285, H_299) | ~m1_connsp_2(F_293, D_269, H_299) | ~r1_tarski(F_293, u1_struct_0(C_237)) | ~m1_subset_1(H_299, u1_struct_0(C_237)) | ~m1_subset_1(H_299, u1_struct_0(D_269)) | ~m1_subset_1(F_293, k1_zfmisc_1(u1_struct_0(D_269))) | ~m1_pre_topc(C_237, D_269) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_269), u1_struct_0(B_173)))) | ~v1_funct_2(E_285, u1_struct_0(D_269), u1_struct_0(B_173)) | ~v1_funct_1(E_285) | ~m1_pre_topc(D_269, A_45) | v2_struct_0(D_269) | ~m1_pre_topc(C_237, A_45) | v2_struct_0(C_237) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.73/2.01  tff(c_1771, plain, (![C_237, B_173, A_45, E_285]: (r1_tmap_1(C_237, B_173, k3_tmap_1(A_45, B_173, '#skF_3', C_237, E_285), '#skF_8') | ~r1_tmap_1('#skF_3', B_173, E_285, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_237)) | ~m1_subset_1('#skF_8', u1_struct_0(C_237)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_237, '#skF_3') | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_173)))) | ~v1_funct_2(E_285, u1_struct_0('#skF_3'), u1_struct_0(B_173)) | ~v1_funct_1(E_285) | ~m1_pre_topc('#skF_3', A_45) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_237, A_45) | v2_struct_0(C_237) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(resolution, [status(thm)], [c_1767, c_20])).
% 5.73/2.01  tff(c_1774, plain, (![C_237, B_173, A_45, E_285]: (r1_tmap_1(C_237, B_173, k3_tmap_1(A_45, B_173, '#skF_3', C_237, E_285), '#skF_8') | ~r1_tmap_1('#skF_3', B_173, E_285, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_237)) | ~m1_subset_1('#skF_8', u1_struct_0(C_237)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_237, '#skF_3') | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_173)))) | ~v1_funct_2(E_285, u1_struct_0('#skF_3'), u1_struct_0(B_173)) | ~v1_funct_1(E_285) | ~m1_pre_topc('#skF_3', A_45) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_237, A_45) | v2_struct_0(C_237) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1771])).
% 5.73/2.01  tff(c_1775, plain, (![C_237, B_173, A_45, E_285]: (r1_tmap_1(C_237, B_173, k3_tmap_1(A_45, B_173, '#skF_3', C_237, E_285), '#skF_8') | ~r1_tmap_1('#skF_3', B_173, E_285, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_237)) | ~m1_subset_1('#skF_8', u1_struct_0(C_237)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_pre_topc(C_237, '#skF_3') | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_173)))) | ~v1_funct_2(E_285, u1_struct_0('#skF_3'), u1_struct_0(B_173)) | ~v1_funct_1(E_285) | ~m1_pre_topc('#skF_3', A_45) | ~m1_pre_topc(C_237, A_45) | v2_struct_0(C_237) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(negUnitSimplification, [status(thm)], [c_50, c_1774])).
% 5.73/2.01  tff(c_1799, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1775])).
% 5.73/2.01  tff(c_1814, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_4, c_1799])).
% 5.73/2.01  tff(c_1830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1814])).
% 5.73/2.01  tff(c_1832, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1775])).
% 5.73/2.01  tff(c_1848, plain, (![A_9]: (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(A_9))) | ~m1_pre_topc('#skF_3', A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_1832, c_10])).
% 5.73/2.01  tff(c_1923, plain, (![A_734, C_735, A_736]: (v3_pre_topc(A_734, C_735) | ~v3_pre_topc(A_734, A_736) | ~m1_pre_topc(C_735, A_736) | ~m1_subset_1(A_734, k1_zfmisc_1(u1_struct_0(A_736))) | ~l1_pre_topc(A_736) | ~r1_tarski(A_734, u1_struct_0(C_735)))), inference(resolution, [status(thm)], [c_4, c_1321])).
% 5.73/2.01  tff(c_1931, plain, (![A_734]: (v3_pre_topc(A_734, '#skF_4') | ~v3_pre_topc(A_734, '#skF_2') | ~m1_subset_1(A_734, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_734, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_44, c_1923])).
% 5.73/2.01  tff(c_2097, plain, (![A_741]: (v3_pre_topc(A_741, '#skF_4') | ~v3_pre_topc(A_741, '#skF_2') | ~m1_subset_1(A_741, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_741, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1931])).
% 5.73/2.01  tff(c_2101, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1848, c_2097])).
% 5.73/2.01  tff(c_2133, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1301, c_28, c_2101])).
% 5.73/2.01  tff(c_2135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1542, c_2133])).
% 5.73/2.01  tff(c_2136, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1538])).
% 5.73/2.01  tff(c_2504, plain, (![C_796, B_798, A_799, E_801]: (r1_tmap_1(C_796, B_798, k3_tmap_1(A_799, B_798, '#skF_4', C_796, E_801), '#skF_8') | ~r1_tmap_1('#skF_4', B_798, E_801, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(C_796, '#skF_4') | ~m1_subset_1(E_801, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_798)))) | ~v1_funct_2(E_801, u1_struct_0('#skF_4'), u1_struct_0(B_798)) | ~v1_funct_1(E_801) | ~m1_pre_topc('#skF_4', A_799) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_796, A_799) | v2_struct_0(C_796) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(resolution, [status(thm)], [c_2136, c_2500])).
% 5.73/2.01  tff(c_2511, plain, (![C_796, B_798, A_799, E_801]: (r1_tmap_1(C_796, B_798, k3_tmap_1(A_799, B_798, '#skF_4', C_796, E_801), '#skF_8') | ~r1_tmap_1('#skF_4', B_798, E_801, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0(C_796)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(C_796, '#skF_4') | ~m1_subset_1(E_801, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_798)))) | ~v1_funct_2(E_801, u1_struct_0('#skF_4'), u1_struct_0(B_798)) | ~v1_funct_1(E_801) | ~m1_pre_topc('#skF_4', A_799) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_796, A_799) | v2_struct_0(C_796) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_2504])).
% 5.73/2.01  tff(c_2512, plain, (![C_796, B_798, A_799, E_801]: (r1_tmap_1(C_796, B_798, k3_tmap_1(A_799, B_798, '#skF_4', C_796, E_801), '#skF_8') | ~r1_tmap_1('#skF_4', B_798, E_801, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_796)) | ~m1_subset_1('#skF_8', u1_struct_0(C_796)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(C_796, '#skF_4') | ~m1_subset_1(E_801, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_798)))) | ~v1_funct_2(E_801, u1_struct_0('#skF_4'), u1_struct_0(B_798)) | ~v1_funct_1(E_801) | ~m1_pre_topc('#skF_4', A_799) | ~m1_pre_topc(C_796, A_799) | v2_struct_0(C_796) | ~l1_pre_topc(B_798) | ~v2_pre_topc(B_798) | v2_struct_0(B_798) | ~l1_pre_topc(A_799) | ~v2_pre_topc(A_799) | v2_struct_0(A_799))), inference(negUnitSimplification, [status(thm)], [c_46, c_2511])).
% 5.73/2.01  tff(c_2815, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_2512])).
% 5.73/2.01  tff(c_2818, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2650, c_2815])).
% 5.73/2.01  tff(c_2840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_36, c_2818])).
% 5.73/2.01  tff(c_3399, plain, (![C_840, B_841, A_842, E_843]: (r1_tmap_1(C_840, B_841, k3_tmap_1(A_842, B_841, '#skF_4', C_840, E_843), '#skF_8') | ~r1_tmap_1('#skF_4', B_841, E_843, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_840)) | ~m1_subset_1('#skF_8', u1_struct_0(C_840)) | ~m1_pre_topc(C_840, '#skF_4') | ~m1_subset_1(E_843, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_841)))) | ~v1_funct_2(E_843, u1_struct_0('#skF_4'), u1_struct_0(B_841)) | ~v1_funct_1(E_843) | ~m1_pre_topc('#skF_4', A_842) | ~m1_pre_topc(C_840, A_842) | v2_struct_0(C_840) | ~l1_pre_topc(B_841) | ~v2_pre_topc(B_841) | v2_struct_0(B_841) | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | v2_struct_0(A_842))), inference(splitRight, [status(thm)], [c_2512])).
% 5.73/2.01  tff(c_3401, plain, (![C_840, A_842]: (r1_tmap_1(C_840, '#skF_1', k3_tmap_1(A_842, '#skF_1', '#skF_4', C_840, '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_840)) | ~m1_subset_1('#skF_8', u1_struct_0(C_840)) | ~m1_pre_topc(C_840, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_842) | ~m1_pre_topc(C_840, A_842) | v2_struct_0(C_840) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | v2_struct_0(A_842))), inference(resolution, [status(thm)], [c_38, c_3399])).
% 5.73/2.01  tff(c_3407, plain, (![C_840, A_842]: (r1_tmap_1(C_840, '#skF_1', k3_tmap_1(A_842, '#skF_1', '#skF_4', C_840, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_840)) | ~m1_subset_1('#skF_8', u1_struct_0(C_840)) | ~m1_pre_topc(C_840, '#skF_4') | ~m1_pre_topc('#skF_4', A_842) | ~m1_pre_topc(C_840, A_842) | v2_struct_0(C_840) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_842) | ~v2_pre_topc(A_842) | v2_struct_0(A_842))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_42, c_40, c_1178, c_3401])).
% 5.73/2.01  tff(c_3452, plain, (![C_848, A_849]: (r1_tmap_1(C_848, '#skF_1', k3_tmap_1(A_849, '#skF_1', '#skF_4', C_848, '#skF_5'), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(C_848)) | ~m1_subset_1('#skF_8', u1_struct_0(C_848)) | ~m1_pre_topc(C_848, '#skF_4') | ~m1_pre_topc('#skF_4', A_849) | ~m1_pre_topc(C_848, A_849) | v2_struct_0(C_848) | ~l1_pre_topc(A_849) | ~v2_pre_topc(A_849) | v2_struct_0(A_849))), inference(negUnitSimplification, [status(thm)], [c_62, c_3407])).
% 5.73/2.01  tff(c_1177, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_72])).
% 5.73/2.01  tff(c_3457, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_3452, c_1177])).
% 5.73/2.01  tff(c_3464, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_44, c_36, c_30, c_24, c_3457])).
% 5.73/2.01  tff(c_3466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_50, c_3464])).
% 5.73/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.01  
% 5.73/2.01  Inference rules
% 5.73/2.01  ----------------------
% 5.73/2.01  #Ref     : 0
% 5.73/2.01  #Sup     : 592
% 5.73/2.01  #Fact    : 0
% 5.73/2.01  #Define  : 0
% 5.73/2.01  #Split   : 14
% 5.73/2.01  #Chain   : 0
% 5.73/2.01  #Close   : 0
% 5.73/2.01  
% 5.73/2.01  Ordering : KBO
% 5.73/2.01  
% 5.73/2.01  Simplification rules
% 5.73/2.01  ----------------------
% 5.73/2.01  #Subsume      : 251
% 5.73/2.01  #Demod        : 946
% 5.73/2.01  #Tautology    : 143
% 5.73/2.01  #SimpNegUnit  : 47
% 5.73/2.01  #BackRed      : 0
% 5.73/2.01  
% 5.73/2.01  #Partial instantiations: 0
% 5.73/2.01  #Strategies tried      : 1
% 5.73/2.01  
% 5.73/2.01  Timing (in seconds)
% 5.73/2.01  ----------------------
% 5.73/2.01  Preprocessing        : 0.41
% 5.73/2.01  Parsing              : 0.21
% 5.73/2.01  CNF conversion       : 0.07
% 5.73/2.01  Main loop            : 0.77
% 5.73/2.01  Inferencing          : 0.27
% 5.73/2.01  Reduction            : 0.26
% 5.73/2.01  Demodulation         : 0.18
% 5.73/2.01  BG Simplification    : 0.03
% 5.73/2.01  Subsumption          : 0.16
% 5.73/2.01  Abstraction          : 0.03
% 5.73/2.01  MUC search           : 0.00
% 5.73/2.01  Cooper               : 0.00
% 5.73/2.01  Total                : 1.26
% 5.73/2.01  Index Insertion      : 0.00
% 5.73/2.01  Index Deletion       : 0.00
% 5.73/2.01  Index Matching       : 0.00
% 5.73/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
