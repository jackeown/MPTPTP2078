%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:27 EST 2020

% Result     : Theorem 3.68s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 207 expanded)
%              Number of leaves         :   33 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  304 (1695 expanded)
%              Number of equality atoms :    5 (  69 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(f_238,negated_conjecture,(
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

tff(f_36,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_180,axiom,(
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
                                   => ( ( v3_pre_topc(F,D)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_63,axiom,(
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

tff(f_123,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_20,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_71,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_24,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_72,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_22,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_87,plain,(
    ! [B_668,A_669] :
      ( l1_pre_topc(B_668)
      | ~ m1_pre_topc(B_668,A_669)
      | ~ l1_pre_topc(A_669) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_87])).

tff(c_102,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_93])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [C_676,A_677,B_678] :
      ( m1_subset_1(C_676,k1_zfmisc_1(u1_struct_0(A_677)))
      | ~ m1_subset_1(C_676,k1_zfmisc_1(u1_struct_0(B_678)))
      | ~ m1_pre_topc(B_678,A_677)
      | ~ l1_pre_topc(A_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_172,plain,(
    ! [A_683,A_684,B_685] :
      ( m1_subset_1(A_683,k1_zfmisc_1(u1_struct_0(A_684)))
      | ~ m1_pre_topc(B_685,A_684)
      | ~ l1_pre_topc(A_684)
      | ~ r1_tarski(A_683,u1_struct_0(B_685)) ) ),
    inference(resolution,[status(thm)],[c_4,c_133])).

tff(c_180,plain,(
    ! [A_683] :
      ( m1_subset_1(A_683,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_683,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_34,c_172])).

tff(c_190,plain,(
    ! [A_683] :
      ( m1_subset_1(A_683,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_683,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_180])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_62,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_110,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_58,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_56,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_38,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_69,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_132,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_69])).

tff(c_404,plain,(
    ! [A_726,D_724,C_728,E_729,F_727,B_730,H_725] :
      ( r1_tmap_1(D_724,B_730,E_729,H_725)
      | ~ r1_tmap_1(C_728,B_730,k3_tmap_1(A_726,B_730,D_724,C_728,E_729),H_725)
      | ~ r1_tarski(F_727,u1_struct_0(C_728))
      | ~ r2_hidden(H_725,F_727)
      | ~ v3_pre_topc(F_727,D_724)
      | ~ m1_subset_1(H_725,u1_struct_0(C_728))
      | ~ m1_subset_1(H_725,u1_struct_0(D_724))
      | ~ m1_subset_1(F_727,k1_zfmisc_1(u1_struct_0(D_724)))
      | ~ m1_pre_topc(C_728,D_724)
      | ~ m1_subset_1(E_729,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_724),u1_struct_0(B_730))))
      | ~ v1_funct_2(E_729,u1_struct_0(D_724),u1_struct_0(B_730))
      | ~ v1_funct_1(E_729)
      | ~ m1_pre_topc(D_724,A_726)
      | v2_struct_0(D_724)
      | ~ m1_pre_topc(C_728,A_726)
      | v2_struct_0(C_728)
      | ~ l1_pre_topc(B_730)
      | ~ v2_pre_topc(B_730)
      | v2_struct_0(B_730)
      | ~ l1_pre_topc(A_726)
      | ~ v2_pre_topc(A_726)
      | v2_struct_0(A_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_408,plain,(
    ! [F_727] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_727,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_727)
      | ~ v3_pre_topc(F_727,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_727,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_132,c_404])).

tff(c_415,plain,(
    ! [F_727] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_727,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_727)
      | ~ v3_pre_topc(F_727,'#skF_4')
      | ~ m1_subset_1(F_727,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58,c_56,c_46,c_42,c_40,c_38,c_36,c_34,c_71,c_28,c_408])).

tff(c_417,plain,(
    ! [F_731] :
      ( ~ r1_tarski(F_731,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_731)
      | ~ v3_pre_topc(F_731,'#skF_4')
      | ~ m1_subset_1(F_731,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_60,c_48,c_44,c_110,c_415])).

tff(c_456,plain,(
    ! [A_732] :
      ( ~ r2_hidden('#skF_8',A_732)
      | ~ v3_pre_topc(A_732,'#skF_4')
      | ~ r1_tarski(A_732,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_190,c_417])).

tff(c_467,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_456])).

tff(c_476,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_467])).

tff(c_227,plain,(
    ! [A_693] :
      ( m1_subset_1(A_693,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_693,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_180])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_249,plain,(
    ! [A_696] :
      ( r1_tarski(A_696,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_696,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_227,c_2])).

tff(c_260,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_249])).

tff(c_26,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_200,plain,(
    ! [D_688,C_689,A_690] :
      ( v3_pre_topc(D_688,C_689)
      | ~ m1_subset_1(D_688,k1_zfmisc_1(u1_struct_0(C_689)))
      | ~ v3_pre_topc(D_688,A_690)
      | ~ m1_pre_topc(C_689,A_690)
      | ~ m1_subset_1(D_688,k1_zfmisc_1(u1_struct_0(A_690)))
      | ~ l1_pre_topc(A_690) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_477,plain,(
    ! [A_733,C_734,A_735] :
      ( v3_pre_topc(A_733,C_734)
      | ~ v3_pre_topc(A_733,A_735)
      | ~ m1_pre_topc(C_734,A_735)
      | ~ m1_subset_1(A_733,k1_zfmisc_1(u1_struct_0(A_735)))
      | ~ l1_pre_topc(A_735)
      | ~ r1_tarski(A_733,u1_struct_0(C_734)) ) ),
    inference(resolution,[status(thm)],[c_4,c_200])).

tff(c_483,plain,(
    ! [A_733] :
      ( v3_pre_topc(A_733,'#skF_4')
      | ~ v3_pre_topc(A_733,'#skF_2')
      | ~ m1_subset_1(A_733,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_733,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_477])).

tff(c_545,plain,(
    ! [A_737] :
      ( v3_pre_topc(A_737,'#skF_4')
      | ~ v3_pre_topc(A_737,'#skF_2')
      | ~ m1_subset_1(A_737,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_737,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_483])).

tff(c_574,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_545])).

tff(c_593,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_26,c_574])).

tff(c_595,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_593])).

tff(c_597,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_760,plain,(
    ! [E_768,A_767,G_771,D_770,B_769,C_772] :
      ( r1_tmap_1(D_770,B_769,k3_tmap_1(A_767,B_769,C_772,D_770,E_768),G_771)
      | ~ r1_tmap_1(C_772,B_769,E_768,G_771)
      | ~ m1_pre_topc(D_770,C_772)
      | ~ m1_subset_1(G_771,u1_struct_0(D_770))
      | ~ m1_subset_1(G_771,u1_struct_0(C_772))
      | ~ m1_subset_1(E_768,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_772),u1_struct_0(B_769))))
      | ~ v1_funct_2(E_768,u1_struct_0(C_772),u1_struct_0(B_769))
      | ~ v1_funct_1(E_768)
      | ~ m1_pre_topc(D_770,A_767)
      | v2_struct_0(D_770)
      | ~ m1_pre_topc(C_772,A_767)
      | v2_struct_0(C_772)
      | ~ l1_pre_topc(B_769)
      | ~ v2_pre_topc(B_769)
      | v2_struct_0(B_769)
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767)
      | v2_struct_0(A_767) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_762,plain,(
    ! [D_770,A_767,G_771] :
      ( r1_tmap_1(D_770,'#skF_1',k3_tmap_1(A_767,'#skF_1','#skF_4',D_770,'#skF_5'),G_771)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_771)
      | ~ m1_pre_topc(D_770,'#skF_4')
      | ~ m1_subset_1(G_771,u1_struct_0(D_770))
      | ~ m1_subset_1(G_771,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_770,A_767)
      | v2_struct_0(D_770)
      | ~ m1_pre_topc('#skF_4',A_767)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767)
      | v2_struct_0(A_767) ) ),
    inference(resolution,[status(thm)],[c_36,c_760])).

tff(c_768,plain,(
    ! [D_770,A_767,G_771] :
      ( r1_tmap_1(D_770,'#skF_1',k3_tmap_1(A_767,'#skF_1','#skF_4',D_770,'#skF_5'),G_771)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_771)
      | ~ m1_pre_topc(D_770,'#skF_4')
      | ~ m1_subset_1(G_771,u1_struct_0(D_770))
      | ~ m1_subset_1(G_771,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_770,A_767)
      | v2_struct_0(D_770)
      | ~ m1_pre_topc('#skF_4',A_767)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_767)
      | ~ v2_pre_topc(A_767)
      | v2_struct_0(A_767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_40,c_38,c_762])).

tff(c_803,plain,(
    ! [D_779,A_780,G_781] :
      ( r1_tmap_1(D_779,'#skF_1',k3_tmap_1(A_780,'#skF_1','#skF_4',D_779,'#skF_5'),G_781)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_781)
      | ~ m1_pre_topc(D_779,'#skF_4')
      | ~ m1_subset_1(G_781,u1_struct_0(D_779))
      | ~ m1_subset_1(G_781,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_779,A_780)
      | v2_struct_0(D_779)
      | ~ m1_pre_topc('#skF_4',A_780)
      | ~ l1_pre_topc(A_780)
      | ~ v2_pre_topc(A_780)
      | v2_struct_0(A_780) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_44,c_768])).

tff(c_596,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_806,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_803,c_596])).

tff(c_809,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_42,c_46,c_71,c_28,c_34,c_597,c_806])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_809])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.68/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.58  
% 3.68/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.59  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.68/1.59  
% 3.68/1.59  %Foreground sorts:
% 3.68/1.59  
% 3.68/1.59  
% 3.68/1.59  %Background operators:
% 3.68/1.59  
% 3.68/1.59  
% 3.68/1.59  %Foreground operators:
% 3.68/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.68/1.59  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.68/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.68/1.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.68/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.68/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.68/1.59  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.68/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.68/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.68/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.68/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.68/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.68/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.68/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.68/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.68/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.68/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.68/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.68/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.68/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.68/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.68/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.68/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.68/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.68/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.68/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.68/1.59  
% 3.68/1.61  tff(f_238, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 3.68/1.61  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.68/1.61  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.68/1.61  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 3.68/1.61  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.68/1.61  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 3.68/1.61  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.68/1.61  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_20, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_71, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 3.68/1.61  tff(c_28, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_24, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_72, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 3.68/1.61  tff(c_22, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_87, plain, (![B_668, A_669]: (l1_pre_topc(B_668) | ~m1_pre_topc(B_668, A_669) | ~l1_pre_topc(A_669))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.68/1.61  tff(c_93, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_87])).
% 3.68/1.61  tff(c_102, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_93])).
% 3.68/1.61  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.68/1.61  tff(c_133, plain, (![C_676, A_677, B_678]: (m1_subset_1(C_676, k1_zfmisc_1(u1_struct_0(A_677))) | ~m1_subset_1(C_676, k1_zfmisc_1(u1_struct_0(B_678))) | ~m1_pre_topc(B_678, A_677) | ~l1_pre_topc(A_677))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.68/1.61  tff(c_172, plain, (![A_683, A_684, B_685]: (m1_subset_1(A_683, k1_zfmisc_1(u1_struct_0(A_684))) | ~m1_pre_topc(B_685, A_684) | ~l1_pre_topc(A_684) | ~r1_tarski(A_683, u1_struct_0(B_685)))), inference(resolution, [status(thm)], [c_4, c_133])).
% 3.68/1.61  tff(c_180, plain, (![A_683]: (m1_subset_1(A_683, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_683, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_34, c_172])).
% 3.68/1.61  tff(c_190, plain, (![A_683]: (m1_subset_1(A_683, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_683, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_180])).
% 3.68/1.61  tff(c_60, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_62, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 3.68/1.61  tff(c_110, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_70])).
% 3.68/1.61  tff(c_58, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_56, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_38, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_68, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_69, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_68])).
% 3.68/1.61  tff(c_132, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_110, c_69])).
% 3.68/1.61  tff(c_404, plain, (![A_726, D_724, C_728, E_729, F_727, B_730, H_725]: (r1_tmap_1(D_724, B_730, E_729, H_725) | ~r1_tmap_1(C_728, B_730, k3_tmap_1(A_726, B_730, D_724, C_728, E_729), H_725) | ~r1_tarski(F_727, u1_struct_0(C_728)) | ~r2_hidden(H_725, F_727) | ~v3_pre_topc(F_727, D_724) | ~m1_subset_1(H_725, u1_struct_0(C_728)) | ~m1_subset_1(H_725, u1_struct_0(D_724)) | ~m1_subset_1(F_727, k1_zfmisc_1(u1_struct_0(D_724))) | ~m1_pre_topc(C_728, D_724) | ~m1_subset_1(E_729, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_724), u1_struct_0(B_730)))) | ~v1_funct_2(E_729, u1_struct_0(D_724), u1_struct_0(B_730)) | ~v1_funct_1(E_729) | ~m1_pre_topc(D_724, A_726) | v2_struct_0(D_724) | ~m1_pre_topc(C_728, A_726) | v2_struct_0(C_728) | ~l1_pre_topc(B_730) | ~v2_pre_topc(B_730) | v2_struct_0(B_730) | ~l1_pre_topc(A_726) | ~v2_pre_topc(A_726) | v2_struct_0(A_726))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.68/1.61  tff(c_408, plain, (![F_727]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_727, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_727) | ~v3_pre_topc(F_727, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_727, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_132, c_404])).
% 3.68/1.61  tff(c_415, plain, (![F_727]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_727, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_727) | ~v3_pre_topc(F_727, '#skF_4') | ~m1_subset_1(F_727, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58, c_56, c_46, c_42, c_40, c_38, c_36, c_34, c_71, c_28, c_408])).
% 3.68/1.61  tff(c_417, plain, (![F_731]: (~r1_tarski(F_731, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_731) | ~v3_pre_topc(F_731, '#skF_4') | ~m1_subset_1(F_731, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_60, c_48, c_44, c_110, c_415])).
% 3.68/1.61  tff(c_456, plain, (![A_732]: (~r2_hidden('#skF_8', A_732) | ~v3_pre_topc(A_732, '#skF_4') | ~r1_tarski(A_732, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_190, c_417])).
% 3.68/1.61  tff(c_467, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_456])).
% 3.68/1.61  tff(c_476, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_467])).
% 3.68/1.61  tff(c_227, plain, (![A_693]: (m1_subset_1(A_693, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_693, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_180])).
% 3.68/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.68/1.61  tff(c_249, plain, (![A_696]: (r1_tarski(A_696, u1_struct_0('#skF_4')) | ~r1_tarski(A_696, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_227, c_2])).
% 3.68/1.61  tff(c_260, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_249])).
% 3.68/1.61  tff(c_26, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 3.68/1.61  tff(c_200, plain, (![D_688, C_689, A_690]: (v3_pre_topc(D_688, C_689) | ~m1_subset_1(D_688, k1_zfmisc_1(u1_struct_0(C_689))) | ~v3_pre_topc(D_688, A_690) | ~m1_pre_topc(C_689, A_690) | ~m1_subset_1(D_688, k1_zfmisc_1(u1_struct_0(A_690))) | ~l1_pre_topc(A_690))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.68/1.61  tff(c_477, plain, (![A_733, C_734, A_735]: (v3_pre_topc(A_733, C_734) | ~v3_pre_topc(A_733, A_735) | ~m1_pre_topc(C_734, A_735) | ~m1_subset_1(A_733, k1_zfmisc_1(u1_struct_0(A_735))) | ~l1_pre_topc(A_735) | ~r1_tarski(A_733, u1_struct_0(C_734)))), inference(resolution, [status(thm)], [c_4, c_200])).
% 3.68/1.61  tff(c_483, plain, (![A_733]: (v3_pre_topc(A_733, '#skF_4') | ~v3_pre_topc(A_733, '#skF_2') | ~m1_subset_1(A_733, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_733, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_477])).
% 3.68/1.61  tff(c_545, plain, (![A_737]: (v3_pre_topc(A_737, '#skF_4') | ~v3_pre_topc(A_737, '#skF_2') | ~m1_subset_1(A_737, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_737, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_483])).
% 3.68/1.61  tff(c_574, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_545])).
% 3.68/1.61  tff(c_593, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_26, c_574])).
% 3.68/1.61  tff(c_595, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_593])).
% 3.68/1.61  tff(c_597, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 3.68/1.61  tff(c_760, plain, (![E_768, A_767, G_771, D_770, B_769, C_772]: (r1_tmap_1(D_770, B_769, k3_tmap_1(A_767, B_769, C_772, D_770, E_768), G_771) | ~r1_tmap_1(C_772, B_769, E_768, G_771) | ~m1_pre_topc(D_770, C_772) | ~m1_subset_1(G_771, u1_struct_0(D_770)) | ~m1_subset_1(G_771, u1_struct_0(C_772)) | ~m1_subset_1(E_768, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_772), u1_struct_0(B_769)))) | ~v1_funct_2(E_768, u1_struct_0(C_772), u1_struct_0(B_769)) | ~v1_funct_1(E_768) | ~m1_pre_topc(D_770, A_767) | v2_struct_0(D_770) | ~m1_pre_topc(C_772, A_767) | v2_struct_0(C_772) | ~l1_pre_topc(B_769) | ~v2_pre_topc(B_769) | v2_struct_0(B_769) | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767) | v2_struct_0(A_767))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.68/1.61  tff(c_762, plain, (![D_770, A_767, G_771]: (r1_tmap_1(D_770, '#skF_1', k3_tmap_1(A_767, '#skF_1', '#skF_4', D_770, '#skF_5'), G_771) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_771) | ~m1_pre_topc(D_770, '#skF_4') | ~m1_subset_1(G_771, u1_struct_0(D_770)) | ~m1_subset_1(G_771, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_770, A_767) | v2_struct_0(D_770) | ~m1_pre_topc('#skF_4', A_767) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767) | v2_struct_0(A_767))), inference(resolution, [status(thm)], [c_36, c_760])).
% 3.68/1.61  tff(c_768, plain, (![D_770, A_767, G_771]: (r1_tmap_1(D_770, '#skF_1', k3_tmap_1(A_767, '#skF_1', '#skF_4', D_770, '#skF_5'), G_771) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_771) | ~m1_pre_topc(D_770, '#skF_4') | ~m1_subset_1(G_771, u1_struct_0(D_770)) | ~m1_subset_1(G_771, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_770, A_767) | v2_struct_0(D_770) | ~m1_pre_topc('#skF_4', A_767) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_767) | ~v2_pre_topc(A_767) | v2_struct_0(A_767))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_40, c_38, c_762])).
% 3.68/1.61  tff(c_803, plain, (![D_779, A_780, G_781]: (r1_tmap_1(D_779, '#skF_1', k3_tmap_1(A_780, '#skF_1', '#skF_4', D_779, '#skF_5'), G_781) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_781) | ~m1_pre_topc(D_779, '#skF_4') | ~m1_subset_1(G_781, u1_struct_0(D_779)) | ~m1_subset_1(G_781, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_779, A_780) | v2_struct_0(D_779) | ~m1_pre_topc('#skF_4', A_780) | ~l1_pre_topc(A_780) | ~v2_pre_topc(A_780) | v2_struct_0(A_780))), inference(negUnitSimplification, [status(thm)], [c_60, c_44, c_768])).
% 3.68/1.61  tff(c_596, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 3.68/1.61  tff(c_806, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_803, c_596])).
% 3.68/1.61  tff(c_809, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_42, c_46, c_71, c_28, c_34, c_597, c_806])).
% 3.68/1.61  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_809])).
% 3.68/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.61  
% 3.68/1.61  Inference rules
% 3.68/1.61  ----------------------
% 3.68/1.61  #Ref     : 0
% 3.68/1.61  #Sup     : 149
% 3.68/1.61  #Fact    : 0
% 3.68/1.61  #Define  : 0
% 3.68/1.61  #Split   : 4
% 3.68/1.61  #Chain   : 0
% 3.68/1.61  #Close   : 0
% 3.68/1.61  
% 3.68/1.61  Ordering : KBO
% 3.68/1.61  
% 3.68/1.61  Simplification rules
% 3.68/1.61  ----------------------
% 3.68/1.61  #Subsume      : 28
% 3.68/1.61  #Demod        : 135
% 3.68/1.61  #Tautology    : 22
% 3.68/1.61  #SimpNegUnit  : 9
% 3.68/1.61  #BackRed      : 0
% 3.68/1.61  
% 3.68/1.61  #Partial instantiations: 0
% 3.68/1.61  #Strategies tried      : 1
% 3.68/1.61  
% 3.68/1.61  Timing (in seconds)
% 3.68/1.61  ----------------------
% 3.68/1.61  Preprocessing        : 0.41
% 3.68/1.61  Parsing              : 0.20
% 3.68/1.61  CNF conversion       : 0.07
% 3.68/1.61  Main loop            : 0.38
% 3.68/1.61  Inferencing          : 0.13
% 3.68/1.61  Reduction            : 0.12
% 3.68/1.61  Demodulation         : 0.08
% 3.68/1.61  BG Simplification    : 0.02
% 3.68/1.61  Subsumption          : 0.08
% 3.68/1.61  Abstraction          : 0.01
% 3.68/1.61  MUC search           : 0.00
% 3.68/1.61  Cooper               : 0.00
% 3.68/1.61  Total                : 0.83
% 3.68/1.61  Index Insertion      : 0.00
% 3.68/1.61  Index Deletion       : 0.00
% 3.68/1.61  Index Matching       : 0.00
% 3.68/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
